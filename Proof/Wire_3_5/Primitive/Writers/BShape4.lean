import Proof.Wire_3_5.Primitive.Writers.BShape3

/-! # (P-b): the batch's shape, part 4: the SYM batch's four facts (`hpre` forms (1)-(4))

Over `symExprs` (the SYM batch's printed rows in C4's order): **`sym_rows_factors`** (row `r` of every entry:
`1` factor for the FILTER rows `r < |carriers|`, `walkLen` for the POP rows), **`sym_factors_ok`** (degree
`≤ max(384·walkLen_F + 1, 3·lbP)`, atoms `< 4·(2^{kh}·2^{kh})·|pool|`), **`sym_coef_pm1`**, **`sym_row_terms_le`**
(`≤ (M+1)²·2^{walkLen}` terms per row).

Paper quantity of the main types: the SYM printed rows' shape (row:sym, P3:1496-1526; alg:compiler's admissible
requests, P3:1886-1906). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Row

section SymB
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- The SYM labels of slice `j` at star row `row < N²`. -/
theorem sym_labs_ok (row j N : ℕ) (hrow : row < N ^ 2) (hj : j < carriers.length + a) :
    LabsOk ((symSlices Cs carriers).getD j []).length
      (CompilerMachine.Pool.labsOf (symPool Cs carriers).length row (sliceGis (symSlices Cs carriers) j))
      (4 * (N * N) * (symPool Cs carriers).length) := by
  have h := labsOf_ok (symPool Cs carriers).length row (sliceGis (symSlices Cs carriers) j)
    ((symSlices Cs carriers).getD j []).length (by rw [sliceGis_length])
    (fun gi hgi => mem_sliceGis_lt _ j (by rw [symSlices_length]; exact hj) gi hgi)
  refine ⟨h.1, fun x hx => lt_of_lt_of_le (h.2 x hx) ?_⟩
  have : row + 1 ≤ N * N := by rw [← sq]; omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)

/-- **(1) Factor counts by row position.** -/
theorem sym_rows_factors : ∀ i r, r < carriers.length + 2 * a →
    SeedFix.Uniform ((symExprs I hs Cs carriers).getD (i * (carriers.length + 2 * a) + r) [])
      (if r < carriers.length then 1 else (symListParams I n a Cs carriers).walkLen) := by
  intro i r hr
  unfold symExprs symBatchE symBatch
  refine rows_uniform _ _ _ _ (fun r => if r < carriers.length then 1 else (symListParams I n a Cs carriers).walkLen)
    (fun t row => symGroups_length _ _ _ _ _ _ _ _ _ _ _) ?_ i r hr
  intro t row r ht hrow hr q hq
  by_cases hc : r < carriers.length
  · rw [symGroups_getD_filt _ _ _ _ _ _ _ _ _ _ _ _ hc, List.mem_singleton] at hq
    subst hq
    simp only [if_pos hc]
    intro tm htm
    unfold filtRow at htm
    rw [filt_ref, List.mem_singleton] at htm
    subst htm
    rfl
  · simp only [if_neg hc]
    obtain ⟨i', sgn, s, rfl⟩ := symGroups_getD_pop _ _ _ _ _ _ _ _ _ _ _ _ (by omega) q hq
    intro tm htm
    exact (mem_popRef _ tm htm).2.1

/-- **(2) Factors**: degree and atoms. -/
theorem sym_factors_ok : ∀ V ∈ symExprs I hs Cs carriers, ∀ t ∈ V, ∀ p ∈ t.2,
    PolyOk (max (384 * (I.filterParams .sym n).walkLen + 1) (3 * PopLink.lbP (symListParams I n a Cs carriers)))
      (4 * (2 ^ SeedFix.callKh (I.starParams n hs) * 2 ^ SeedFix.callKh (I.starParams n hs)) *
        (symPool Cs carriers).length) p := by
  unfold symExprs
  apply terms_of_reqs (fun t => ∀ p ∈ t.2, PolyOk _ _ p)
  intro g hg q hq t ht p hp
  unfold symBatchE symBatch at hg
  obtain ⟨tt, row, _, hrow, hg'⟩ := mem_batchOf hg
  rcases mem_symGroups hg' with ⟨j, hj, rfl⟩ | ⟨i, sgn, mm, t2, rfl⟩
  · rw [List.mem_singleton] at hq
    subst hq
    have hl := sym_labs_ok Cs carriers row j _ hrow (by omega)
    exact ((filtRow_ok _ _ _ _ _ _ _ _ hl t ht).2.2 p hp).mono (le_max_left _ _) le_rfl
  · obtain ⟨s, rfl⟩ := mem_popFactor hq
    have hl := sym_labs_ok Cs carriers row (carriers.length + i) _ hrow (by omega)
    exact ((popRow_ok _ _ _ _ _ _ _ _ _ _ hl t ht).2.2 p hp).mono (le_max_right _ _) le_rfl

/-- **(3) Coefficients `±1`.** -/
theorem sym_coef_pm1 : ∀ V ∈ symExprs I hs Cs carriers, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1 := by
  unfold symExprs
  apply terms_of_reqs
  intro g hg q hq t ht
  unfold symBatchE symBatch at hg
  obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
  rcases mem_symGroups hg' with ⟨j, hj, rfl⟩ | ⟨i, sgn, mm, t2, rfl⟩
  · rw [List.mem_singleton] at hq
    subst hq
    unfold filtRow at ht
    rw [filt_ref, List.mem_singleton] at ht
    subst ht
    left; rfl
  · obtain ⟨s, rfl⟩ := mem_popFactor hq
    exact (mem_popRef _ t ht).1

/-- **(4) Term counts per row.** -/
theorem sym_row_terms_le : ∀ V ∈ symExprs I hs Cs carriers,
    V.length ≤ ((symListParams I n a Cs carriers).M + 1) ^ 2 * 2 ^ (symListParams I n a Cs carriers).walkLen := by
  unfold symExprs
  apply rows_length_le
  intro g hg
  unfold symBatchE symBatch at hg
  obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
  have hX : 1 ≤ 2 ^ (symListParams I n a Cs carriers).walkLen := Nat.one_le_two_pow
  rcases mem_symGroups hg' with ⟨j, hj, rfl⟩ | ⟨i, sgn, mm, t2, rfl⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    unfold filtRow
    rw [filt_ref]
    simp only [List.length_singleton, Nat.add_zero]
    have : 1 ≤ ((symListParams I n a Cs carriers).M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  · have h1 := sum_map_le_card (popFactor (symSlices Cs carriers) (symListParams I n a Cs carriers)
      (symEnum I hs Cs carriers tt).1.2 (symPool Cs carriers).length row n (carriers.length + i) sgn mm t2)
      (fun r => (refOf r).length) (1 + (symListParams I n a Cs carriers).M *
      2 ^ (symListParams I n a Cs carriers).walkLen) (fun q hq => by
        obtain ⟨s, rfl⟩ := mem_popFactor hq
        exact popRow_length _ _ _ _ _ _ _ _ _)
    have h2 := popFactor_length (symSlices Cs carriers) (symListParams I n a Cs carriers)
      (symEnum I hs Cs carriers tt).1.2 (symPool Cs carriers).length row n (carriers.length + i) sgn mm t2
    set M := (symListParams I n a Cs carriers).M
    set X := 2 ^ (symListParams I n a Cs carriers).walkLen
    have h3 : 1 + M * X ≤ (M + 1) * X := by nlinarith
    have h4 := Nat.mul_le_mul h2 h3
    calc _ ≤ _ := h1
      _ ≤ (M + 1) * ((M + 1) * X) := by
          apply le_trans (Nat.mul_le_mul_right _ h2); exact Nat.mul_le_mul_left _ h3
      _ = (M + 1) ^ 2 * X := by ring

end SymB

end NearCubicWires.WireExponent3_5.PrimAsm.BShape
