import Proof.Wire_3_5.FinalPass.HashShape
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.Primitive.Writers.BShape6

/-! # The HASH rows' shape and the HASH tape's word (`filt:soft`, P3:2220-2290; row:filter P3:2063-2101)

The HASH tape's rows are aux FILTER rows (`hashRow`, one term with one factor `filtPolyC`) over the carriers' prefix
of the pool (gates `< 2Σ|X_j| ≤ G`) at star row `row < N²`: every monomial has at most `384·w_aux + 1` atoms, each
below `4N²G` (the corner pool's atom range), and the factor has at most `(8Σ|X_j| + 1)^{384 w_aux + 1}` monomials
(`Print.goods_length_le`, P3:1484-1486). The corner forms `Z^±` (`zPoly`) have at most `3` atoms below `4(row+1)G`.
So every factor of every printed HASH term is of the pool's shape, and the HASH tape's word has at most
`|Fs|·(PW + 12) + 1` bits when every row's polynomial word has at most `PW`.

* `filtRow_poly`, `hashRow_poly`, **`hashFs_mem`**, `hashFs_getD`, `zPoly_ok`, **`hashFactor_ok`**, **`htWord_le`**.

Paper quantities of the main types: the printed HASH factors' degrees and atoms, and the HASH tape's length. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.BShape NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.ListMachine.Row

section Rows
variable (P : StarParams) (carriers : List (Stars.Carrier P.n)) (FP : GapParams) (e : ℕ)

/-- **A FILTER row's polynomial**: degree `≤ 384·w + 1`, atoms below `A`, at most `(4L+1)^{384 w + 1}` monomials. -/
theorem filtRow_poly (r : FiltReq) (A : ℕ) (h : LabsOk r.L r.labs A) :
    PolyOk (384 * r.P.walkLen + 1) A (filtPolyC r.thr r.tbl r.L r.sgn r.labs) ∧
      (filtPolyC r.thr r.tbl r.L r.sgn r.labs).length ≤ (4 * r.L + 1) ^ (384 * r.P.walkLen + 1) := by
  have hsh := (filt_shape r A h).2
  have hl := factorPoly_length_le (filtF r.thr r.tbl r.sgn) r.L (filtDeg r.tbl) r.labs
  have e : filtPolyC r.thr r.tbl r.L r.sgn r.labs = factorPoly (filtF r.thr r.tbl r.sgn) (4 * r.L) (filtDeg r.tbl) r.labs :=
    rfl
  rw [← e, filtDeg_req] at hl
  rw [filtDeg_req] at hsh
  exact ⟨hsh, hl⟩

/-- **One aux FILTER row's polynomial** (the HASH tape's row at star row `row`). -/
theorem hashRow_poly (e' : GapSeed (Primitive.thrAux P carriers FP e)) (G row nw : ℕ)
    (hG : 2 * (carriers.map List.length).sum ≤ G) :
    PolyOk (384 * (Primitive.thrAux P carriers FP e).walkLen + 1) (4 * (row + 1) * G)
        (PrimT.C4H.rowPoly (hashRow P carriers FP e e' G row nw)) ∧
      (PrimT.C4H.rowPoly (hashRow P carriers FP e e' G row nw)).length ≤
        (4 * (2 * (carriers.map List.length).sum) + 1) ^ (384 * (Primitive.thrAux P carriers FP e).walkLen + 1) :=
  filtRow_poly ⟨Primitive.thrAux P carriers FP e, e', ⟨2 * (carriers.map List.length).sum, true,
    CompilerMachine.Pool.labsOf G row (List.range (2 * (carriers.map List.length).sum)), nw⟩⟩ _
    (labsOf_ok G row (List.range (2 * (carriers.map List.length).sum)) (2 * (carriers.map List.length).sum)
      (by simp) (fun gi h => by rw [List.mem_range] at h; omega))

/-- **Every row of the HASH tape** has the pool's shape (atoms below `4N²G`). -/
theorem hashFs_mem (N nE : ℕ) (enumE : ℕ → GapSeed (Primitive.thrAux P carriers FP e)) (G nw : ℕ)
    (hG : 2 * (carriers.map List.length).sum ≤ G) :
    ∀ p ∈ (hashBatch P carriers FP e N nE enumE G nw).map PrimT.C4H.rowPoly,
      PolyOk (384 * (Primitive.thrAux P carriers FP e).walkLen + 1) (4 * N ^ 2 * G) p ∧
        p.length ≤ (4 * (2 * (carriers.map List.length).sum) + 1) ^
          (384 * (Primitive.thrAux P carriers FP e).walkLen + 1) := by
  intro p hp
  unfold hashBatch at hp
  rw [List.map_map] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hq
  have hnE : 0 < nE := by
    rcases Nat.eq_zero_or_pos nE with h | h
    · rw [h, Nat.mul_zero] at hq; omega
    · exact h
  have hrow : q / nE < N ^ 2 := (Nat.div_lt_iff_lt_mul hnE).mpr hq
  obtain ⟨h1, h2⟩ := hashRow_poly P carriers FP e (enumE (q % nE)) G (q / nE) nw hG
  refine ⟨h1.mono le_rfl ?_, h2⟩
  have : q / nE + 1 ≤ N ^ 2 := hrow
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)

theorem hashFs_getD (N nE : ℕ) (enumE : ℕ → GapSeed (Primitive.thrAux P carriers FP e)) (G nw : ℕ)
    (hG : 2 * (carriers.map List.length).sum ≤ G) (i : ℕ) :
    PolyOk (384 * (Primitive.thrAux P carriers FP e).walkLen + 1) (4 * N ^ 2 * G)
      (((hashBatch P carriers FP e N nE enumE G nw).map PrimT.C4H.rowPoly).getD i []) := by
  by_cases hi : i < ((hashBatch P carriers FP e N nE enumE G nw).map PrimT.C4H.rowPoly).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact (hashFs_mem P carriers FP e N nE enumE G nw hG _ (List.getElem_mem hi)).1
  · rw [List.getD_eq_default _ _ (by omega)]
    intro m hm
    simp at hm

end Rows

/-- The corner forms `Z^±` of pool gate `gi < G` at star row `q`: at most `3` atoms, below `4(q+1)G`. -/
theorem zPoly_ok (G q : ℕ) (sgn : Bool) (gi : ℕ) (hgi : gi < G) :
    PolyOk 3 (4 * (q + 1) * G) (PrimT.HashB.zPoly G q sgn gi) := by
  intro m hm
  unfold PrimT.HashB.zPoly at hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
  have hz : ∀ m1 ∈ (if sgn then Stars.zPlusF2 else Stars.zMinusF2), m1.length ≤ 3 := by
    cases sgn <;> decide
  have hl := hz m0 hm0
  refine ⟨by simpa using hl, fun x hx => ?_⟩
  simp at hx
  obtain ⟨k, _, rfl⟩ := hx
  unfold CompilerMachine.Pool.poolIndex
  have hk := k.isLt
  have h1 : (4 * q + (k : ℕ)) * G ≤ (4 * q + 3) * G := Nat.mul_le_mul_right _ (by omega)
  have e1 : 4 * (q + 1) * G = (4 * q + 3) * G + G := by ring
  omega

/-- **Every factor of every printed HASH term** has the pool's shape. -/
theorem hashFactor_ok (MP : MajorantParams) (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ))
    (plen pre D A : ℕ) (h3 : 3 ≤ D) (hA : 4 * N ^ 2 * G ≤ A) (hFs : ∀ i, PolyOk D A (Fs.getD i []))
    (hpop : ∀ pop ∈ pops, ∀ gi ∈ pop.2, gi < G) :
    ∀ t ∈ PrimT.HashB.hashTermsM MP G N nE Fs pops plen pre, ∀ f ∈ t.2, PolyOk D A f := by
  intro t ht f hf
  obtain ⟨q, hq, e, _, p, hp, hfac⟩ := hashTerm_factors MP G N nE Fs pops plen pre t ht
  rcases hfac f hf with rfl | ⟨gi, hgi, rfl⟩
  · exact hFs _
  · have hmem : PrimT.HashB.popOf pops p ∈ pops := by
      unfold PrimT.HashB.popOf; rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp
    have hq1 : 4 * (q + 1) * G ≤ 4 * N ^ 2 * G := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)
    exact (zPoly_ok G q _ gi (hpop _ hmem gi hgi)).mono h3 (hq1.trans hA)

/-- **The HASH tape's word**: `|htWord Fs| ≤ |Fs|·(PW + 12) + 1` when every row's polynomial word has `≤ PW` bits. -/
theorem htWord_le (Fs : List (F2Poly ℕ)) (PW : ℕ) (h : ∀ p ∈ Fs, (ListMachine.Rec.polyWord p).length ≤ PW) :
    (PrimT.HbM.htWord Fs).length ≤ Fs.length * (PW + 12) + 1 := by
  unfold PrimT.HbM.htWord SeedFix.blockWord
  rw [List.length_append, List.length_flatMap, List.length_singleton, List.map_map]
  have hs := sum_map_le_card Fs (fun p => (SeedFix.entryRec [[((1 : ℤ), [p])]]).length) (PW + 12) (fun p hp => by
    have ht := termWord_le ((1 : ℤ), [p]) 1 PW (Or.inl rfl) (by simp) (fun f hf => by
      rw [List.mem_singleton.mp hf]; exact h p hp)
    have he := exprWord_le [((1 : ℤ), [p])] 1 (1 * (PW + 1) + 6) (by simp) (fun t htm => by
      rw [List.mem_singleton.mp htm]; exact ht)
    show (true :: ([[((1 : ℤ), [p])]].flatMap SeedFix.rowRec ++ [false])).length ≤ _
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, SeedFix.rowRec, List.length_cons,
      List.length_append, List.length_singleton, List.length_nil]
    omega)
  exact Nat.add_le_add_right hs 1

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
