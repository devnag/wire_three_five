import Proof.Wire_3_5.FinalPass.SampShape

/-! # The child's printed objective (mode-generic), part 2: coefficients and term count

The coefficient term of a walk group is `(−N²)^{|β|}·count` with `count ≤ 2^{8ℓ}` (the elimination count of `samp:seed`,
`2^{rest−rank}` or `0`, P3:2950-2957), so with `±1` row coefficients every coefficient of the child expression is at
most `N^{16}·2^{8ℓ}` (alg:compiler's `b` bits, P3:1882-1887); with single-term rows the expression has at most
`n_T·N^8·2^{8ℓ}·2^8` terms (its `A`).
* `cnt_le`, `PM`, `CoefLe`, **`coefLe_sampTerms`**; `length_smul`, `length_sfold_le`, **`length_sampTerms_le`**.
Paper quantities of the main types: the child's `b` and `A` of alg:compiler. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SampShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Sampler Finset

theorem condProb_le (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    (JoinElimination.condProbGauss p ℓ twoH k plen pre cons).1 ≤ 2 ^ (twoH * ℓ) := by
  unfold JoinElimination.condProbGauss
  dsimp only
  split
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact Nat.zero_le _

theorem cnt_le (P : SeedParams) (plen pre : ℕ) (α : Fin 8 → ℕ) (w : Fin 8 → Fin P.N) (β : Fin 8 → Bool) :
    cntL P plen pre α w β ≤ 2 ^ (8 * P.ell) := condProb_le _ _ _ _ _ _ _

/-- Every coefficient is `±1`. -/
def PM (V : SExpr) : Prop := ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1

/-- Every coefficient is at most `B` in size. -/
def CoefLe (B : ℕ) (V : SExpr) : Prop := ∀ t ∈ V, t.1.natAbs ≤ B

theorem CoefLe.smul_pm {B : ℕ} {V W : SExpr} (hV : CoefLe B V) (hW : PM W) : CoefLe B (smul V W) := by
  intro t ht
  unfold SeedFix.smul at ht
  obtain ⟨x, hx, hxt⟩ := List.mem_flatMap.mp ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxt
  rcases hW y hy with h | h <;> simp [h, Int.natAbs_mul] <;> exact hV x hx

theorem CoefLe.sfold_pm {B : ℕ} : ∀ (L : List SExpr) (A : SExpr), CoefLe B A → (∀ V ∈ L, PM V) →
    CoefLe B (SeedFix.sfold A L)
  | [], A, hA, _ => by simpa [SeedFix.sfold] using hA
  | V :: L, A, hA, hL => by
    show CoefLe B (SeedFix.sfold (SeedFix.smul A V) L)
    exact CoefLe.sfold_pm L _ (hA.smul_pm (hL V List.mem_cons_self)) (fun W hW => hL W (List.mem_cons_of_mem _ hW))

theorem CoefLe.flatMap {B : ℕ} {β : Type} (l : List β) (f : β → SExpr) (h : ∀ b ∈ l, CoefLe B (f b)) :
    CoefLe B (l.flatMap f) := by
  intro t ht
  obtain ⟨b, hb, htb⟩ := List.mem_flatMap.mp ht
  exact h b hb t htb

theorem row_pm (batch : List SExpr) (hb : ∀ V ∈ batch, PM V) (i : ℕ) : PM (batch.getD i []) := by
  rcases Nat.lt_or_ge i batch.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; intro t ht; simp at ht

theorem coefTerm_le (P : SeedParams) (β : Fin 8 → Bool) (cnt : ℕ) (hc : cnt ≤ 2 ^ (8 * P.ell)) :
    CoefLe (P.N ^ 16 * 2 ^ (8 * P.ell)) (coefTerm P β cnt) := by
  intro t ht
  simp only [coefTerm, List.mem_singleton] at ht
  subst ht
  have hcard : (univ.filter fun k => β k = true).card ≤ 8 := by
    calc _ ≤ (univ : Finset (Fin 8)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 8 := by simp
  have hNa : ((P.N : ℤ)).natAbs = P.N := by simp
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, hNa]
  have hNc : ((cnt : ℤ)).natAbs = cnt := by simp
  rw [hNc]
  have hN : 1 ≤ P.N := Nat.one_le_two_pow
  have h1 : (P.N ^ 2) ^ (univ.filter fun k => β k = true).card ≤ (P.N ^ 2) ^ 8 :=
    Nat.pow_le_pow_right (Nat.one_le_pow _ _ hN) hcard
  have h2 : (P.N ^ 2) ^ 8 = P.N ^ 16 := by rw [← pow_mul]
  rw [h2] at h1
  exact Nat.mul_le_mul h1 hc

/-- **Every coefficient of the child expression is at most `N^{16}·2^{8ℓ}`** when the rows' coefficients are `±1`. -/
theorem coefLe_sampTerms (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (plen pre : ℕ)
    (hb : ∀ V ∈ batch, PM V) : CoefLe (P.N ^ 16 * 2 ^ (8 * P.ell)) (sampTerms P nT R batch plen pre) := by
  unfold sampTerms sampTermsT
  refine CoefLe.flatMap _ _ fun t _ => CoefLe.flatMap _ _ fun w _ => CoefLe.flatMap _ _ fun α' _ => ?_
  split_ifs
  · refine CoefLe.flatMap _ _ fun β' _ => ?_
    split_ifs
    · intro t ht; simp at ht
    · unfold termsAt
      refine CoefLe.sfold_pm _ _ (coefTerm_le P _ _ (cnt_le P _ _ _ _ _)) ?_
      intro V hV
      unfold walkRows at hV
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hV
      unfold entryRows at hk
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hk
      exact row_pm batch hb _
  · intro t ht; simp at ht

/-! ## The term count -/

theorem length_smul (V W : SExpr) : (smul V W).length = V.length * W.length := by
  unfold SeedFix.smul
  induction V with
  | nil => simp
  | cons t V ih => rw [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_cons]; ring

theorem length_flatMap_le {β : Type} (l : List β) (f : β → SExpr) (B : ℕ) (h : ∀ b ∈ l, (f b).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have := h b List.mem_cons_self
    have := ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    omega

end NearCubicWires.WireExponent3_5.FinalPass.SampShape

