import Proof.Wire_3_5.FinalPass.SampShape2

/-! # The child request's precondition (mode-generic): `C3Req.Pre` from its parts

"Suppose `0 ≤ V(z) ≤ J` on every column [...] `m,d≥1`, each `p_{ν,j}` [...] of degree at most `d` in the threshold pool,
and each `c_ν` has at most `b` bits" and "`log₂A + m + log₂Q' + Q'd·log₂(P_ex+1) ≤ n_out/100`" (alg:compiler,
alg:eq-budget, P3:1882-1900): the child request `C4Child.chR R0 P nT R batch p'` (the call's request with the child's
printed objective `sampTerms`) meets `C3Req.Pre` from the batch's shape (`BatchFacts`), the pool's fits, the request's
numbers and the printer's budget.
* `BatchFacts`, `length_sfold_pow`, **`length_sampTerms_leT`** (rows of `≤ T` terms);
* **`occ_of`** (the printer's gate budget from `2^{eV}` terms and a `2^{eD}` dense pool);
* **`pre_of`** (`C3Req.Pre` of the child request).
Paper quantities of the main types: the child request's `A`, `m`, `d`, `b`, `Q'` and the budget of alg:eq-budget. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SampShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Sampler Finset
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- **The batch's shape**: row `r` of every entry has `f r` factors per term; every monomial of every factor has at
most `D` atoms, each below `A`; every coefficient is `±1`; every row has at most `T` terms. -/
structure BatchFacts (batch : List SExpr) (R : ℕ) (f : ℕ → ℕ) (D A T : ℕ) : Prop where
  fac : ∀ i r, r < R → Uniform (batch.getD (i * R + r) []) (f r)
  mono : ∀ V ∈ batch, FacOk (fun p => ∀ mono ∈ p, mono.length ≤ D ∧ ∀ x ∈ mono, x < A) V
  pm : ∀ V ∈ batch, PM V
  len : ∀ V ∈ batch, V.length ≤ T

theorem length_sfold_pow (T : ℕ) : ∀ (L : List SExpr) (A : SExpr), (∀ V ∈ L, V.length ≤ T) →
    (SeedFix.sfold A L).length ≤ A.length * T ^ L.length
  | [], A, _ => by simp [SeedFix.sfold]
  | V :: L, A, hL => by
    show (SeedFix.sfold (SeedFix.smul A V) L).length ≤ _
    refine (length_sfold_pow T L _ fun W hW => hL W (List.mem_cons_of_mem _ hW)).trans ?_
    rw [length_smul, List.length_cons, pow_succ]
    have := hL V List.mem_cons_self
    calc A.length * V.length * T ^ L.length ≤ A.length * T * T ^ L.length :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
      _ = A.length * (T ^ L.length * T) := by ring

theorem row_lenT (batch : List SExpr) (T : ℕ) (hb : ∀ V ∈ batch, V.length ≤ T) (i : ℕ) :
    (batch.getD i []).length ≤ T := by
  rcases Nat.lt_or_ge i batch.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; simp

/-- **The child expression has at most `n_T·N^8·((2^ℓ)^8·2^8)·T^{8R}` terms** when every row has `≤ T` terms. -/
theorem length_sampTerms_leT (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (plen pre T : ℕ)
    (hb : ∀ V ∈ batch, V.length ≤ T) :
    (sampTerms P nT R batch plen pre).length ≤ nT * (P.N ^ 8 * ((2 ^ P.ell) ^ 8 * (2 ^ 8 * T ^ (8 * R)))) := by
  unfold sampTerms
  have hd : ∀ m : ℕ, (digitsL m).length = m ^ 8 := fun m => by simp [digitsL]
  calc (List.flatMap (sampTermsT P R batch plen pre) (List.range nT)).length
      ≤ (List.range nT).length * (P.N ^ 8 * ((2 ^ P.ell) ^ 8 * (2 ^ 8 * T ^ (8 * R)))) :=
        length_flatMap_le _ _ _ fun t _ => ?_
    _ = _ := by rw [List.length_range]
  unfold sampTermsT
  refine (length_flatMap_le _ _ ((2 ^ P.ell) ^ 8 * (2 ^ 8 * T ^ (8 * R))) fun w _ => ?_).trans (by rw [hd])
  refine (length_flatMap_le _ _ (2 ^ 8 * T ^ (8 * R)) fun α' _ => ?_).trans (by rw [hd])
  split_ifs
  · refine (length_flatMap_le _ _ (T ^ (8 * R)) fun β' _ => ?_).trans (by rw [hd])
    split_ifs
    · simp
    · unfold termsAt
      have hw : (walkRows P batch R w t).length = 8 * R := by
        unfold walkRows entryRows
        rw [List.length_flatMap]
        simp
        ring
      refine (length_sfold_pow T _ _ fun V hV => ?_).trans (by rw [hw]; simp [coefTerm])
      unfold walkRows at hV
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hV
      unfold entryRows at hk
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hk
      exact row_lenT batch T hb _
  · simp

/-! ## The printer's budget and the precondition -/

/-- **The printer's gate budget** from `2^{eV}` terms and a dense pool of `< 2^{eD}` children, when
`10·(2(eV + m + Q' + Q'·d·eD) + 2) ≤ dRow` (alg:eq-budget, P3:1897-1900). -/
theorem occ_of (a : RepairRepresentation.DecompositionAlgorithm) (R : Req.C3Req) (eV eD : ℕ)
    (hV : R.V.length ≤ 2 ^ eV) (hD : (R.D a).flatten.length + 1 ≤ 2 ^ eD)
    (h : 10 * (2 * (eV + R.m + R.P.Q + R.P.Q * R.d * eD) + 2) ≤ R.dRow) :
    (2 * R.occBound a) * (2 * R.occBound a) ≤ SourceInterfaces.rectangularInnerDimension (2 ^ R.dRow) := by
  obtain ⟨E, hE⟩ : ∃ E, E = eV + R.m + R.P.Q + R.P.Q * R.d * eD := ⟨_, rfl⟩
  have hQ : R.P.Q ≤ 2 ^ R.P.Q := (Nat.lt_two_pow_self).le
  have hDp : ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d) ≤ 2 ^ (R.P.Q * R.d * eD) := by
    calc _ ≤ (2 ^ eD) ^ (R.P.Q * R.d) := Nat.pow_le_pow_left hD _
      _ = 2 ^ (R.P.Q * R.d * eD) := by rw [← pow_mul, Nat.mul_comm eD]
  have hocc : R.occBound a ≤ 2 ^ E := by
    unfold Req.C3Req.occBound
    rw [hE, pow_add, pow_add, pow_add]
    calc R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d))
        ≤ 2 ^ eV * 2 ^ R.m * (2 ^ R.P.Q * 2 ^ (R.P.Q * R.d * eD)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hV) (Nat.mul_le_mul hQ hDp)
      _ = _ := by ring
  have h2 : (2 * R.occBound a) * (2 * R.occBound a) ≤ 2 ^ (2 * E + 2) := by
    have e : 2 ^ (2 * E + 2) = (2 * 2 ^ E) * (2 * 2 ^ E) := by
      rw [show 2 * E + 2 = E + E + 2 by ring, pow_add, pow_add]; ring
    rw [e]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hocc) (Nat.mul_le_mul_left _ hocc)
  refine h2.trans ?_
  unfold SourceInterfaces.rectangularInnerDimension
  exact SourceInterfaces.pow_le_integerCeilRoot_of_mul_le (by norm_num) (by norm_num) (by rw [← hE] at h; omega) le_rfl

/-- **The child request meets `C3Req.Pre`** from the batch's shape and the request's numbers. -/
theorem pre_of (a : RepairRepresentation.DecompositionAlgorithm) (R0 : Req.C3Req) (P : SeedParams) (nT Rn : ℕ)
    (batch : List SExpr) (p' : List Bool) (f : ℕ → ℕ) (D A T : ℕ) (hB : BatchFacts batch Rn f D A T)
    (hPP : R0.P.Pre) (hm1 : 1 ≤ R0.m) (hQ : 1 ≤ R0.P.Q) (hmf : 8 * ((List.range Rn).map f).sum = R0.m)
    (hD : D ≤ R0.d) (hA : A ≤ R0.P.flips.length * R0.P.gates.length)
    (hpn : Req.PNFit a R0.P) (hdf : Req.DenseFit R0.P.h (R0.D a)) (hhqd : R0.P.h * R0.P.Q * R0.d ≤ R0.p)
    (hcoef : P.N ^ 16 * 2 ^ (8 * P.ell) * 2 ^ R0.P.Q ≤ 2 ^ R0.p)
    (hw : R0.P.width ≤ 2 * R0.dRow) (hcl : R0.cols.length = R0.dRow) (hcv : ∀ c ∈ R0.cols, c < 2 ^ R0.P.width)
    (hocc : (2 * (PrimT.C4Child.chR R0 P nT Rn batch p').occBound a) *
      (2 * (PrimT.C4Child.chR R0 P nT Rn batch p').occBound a) ≤
        SourceInterfaces.rectangularInnerDimension (2 ^ R0.dRow)) :
    (PrimT.C4Child.chR R0 P nT Rn batch p').Pre a := by
  have hU := uniform_sampTerms P nT Rn batch p'.length (SeedFix.listNum p') f hB.fac
  have hF := facOk_sampTerms _ P nT Rn batch p'.length (SeedFix.listNum p') hB.mono
  have hC := coefLe_sampTerms P nT Rn batch p'.length (SeedFix.listNum p') hB.pm
  refine ⟨hPP, hm1, hQ, ?_, ?_, hpn, hdf, hhqd, ?_, hw, hcl, hcv, hocc⟩
  · intro t ht
    show t.2.length = R0.m
    rw [← hmf]; exact hU t ht
  · intro t ht p hp mono hmono
    obtain ⟨h1, h2⟩ := hF t ht p hp mono hmono
    exact ⟨h1.trans hD, fun x hx => lt_of_lt_of_le (h2 x hx) hA⟩
  · intro t ht
    have := hC t ht
    exact le_trans (Nat.mul_le_mul_right _ this) hcoef

end NearCubicWires.WireExponent3_5.FinalPass.SampShape

