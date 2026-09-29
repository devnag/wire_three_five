import Proof.Wire_3_5.Primitive.Writers.BShape4

/-! # (P-b): the batch's shape, part 5: the THR batch (`thrExprs`, the THR side condition `hpre`)

The THR entry's rows (`thrGroups`): `|carriers|` FILTER rows then the RADIX row of `(g, p, s)` over
the fixed hash's list data. Over `thrExprs`: **`thr_rows_factors`** (row `r`: `1` factor for FILTER, `2·digits` for
RADIX), **`thr_factors_ok`** (degree `≤ max(384·walkLen_F + 1, 3·listBound D)`, atoms `< 4·(2^{kh}·2^{kh})·|pool|`),
**`thr_coef_one`** (every coefficient is `1`), **`thr_row_terms_le`** (`≤ ((M_D+1)²)^{digits}` terms per row).

Paper quantity of the main types: the THR printed rows' shape (row:radix P3:2608-2614; alg:compiler's admissible
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

section ThrB
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPrime

/-- The occurrence slice's indices lie in the THR pool. -/
theorem thrDigGis_lt (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) :
    ∀ gi ∈ thrDigGis P Cs carriers algorithm den g pr d, gi < (thrPool P Cs carriers).length := by
  intro gi hgi
  unfold thrDigGis at hgi
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hgi
  rw [(List.mem_replicate.mp hi).2]
  have hj : carriers.length < (thrSlices P Cs carriers).length := by simp [thrSlices]
  have hsl : (thrSlices P Cs carriers).getD carriers.length [] = (thrOccs P Cs).map (·.gate) := by
    unfold thrSlices
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have h := sliceOff_add_le (thrSlices P Cs carriers) carriers.length hj
  rw [hsl, List.length_map] at h
  have hi' := i.isLt
  unfold thrOff
  exact lt_of_lt_of_le (by omega) h

/-- **The RADIX row request's terms**: coefficient `1`, `2·digits` factors, each of degree `3·listBound D` over the
digits' labels. -/
theorem radRow_ok (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (D : ListData) (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val)
    (row nw : ℕ) :
    ∀ t ∈ refOf (radRow P Cs carriers algorithm den D g pr s (thrPool P Cs carriers).length row nw),
      t.1 = 1 ∧ t.2.length = 2 * thrDigits P Cs algorithm den ∧
      ∀ p ∈ t.2, PolyOk (3 * listBound D) (4 * (row + 1) * (thrPool P Cs carriers).length) p := by
  intro t ht
  have h := rad_terms ⟨D, thrDigs P Cs carriers algorithm den g pr (thrPool P Cs carriers).length row, pr.val, 2,
    s.val, nw⟩ (4 * (row + 1) * (thrPool P Cs carriers).length) (by
      intro dg hdg
      unfold thrDigs at hdg
      obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hdg
      exact labsOf_ok _ row _ _ le_rfl (thrDigGis_lt P Cs carriers algorithm den g pr d)) t ht
  refine ⟨h.1, ?_, h.2.2⟩
  rw [h.2.1]
  simp [thrDigs]

theorem radRow_length (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (D : ListData) (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val)
    (G row nw : ℕ) :
    (refOf (radRow P Cs carriers algorithm den D g pr s G row nw)).length ≤
      ((D.M + 1) ^ 2) ^ thrDigits P Cs algorithm den := by
  have e : (thrDigs P Cs carriers algorithm den g pr G row).length = thrDigits P Cs algorithm den := by simp [thrDigs]
  have h := rad_length ⟨D, thrDigs P Cs carriers algorithm den g pr G row, pr.val, 2, s.val, nw⟩
  change _ ≤ ((D.M + 1) ^ 2) ^ (thrDigs P Cs carriers algorithm den g pr G row).length at h
  rw [e] at h
  exact h

theorem thrSlices_length (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) : (thrSlices P Cs carriers).length = carriers.length + 1 := by
  simp [thrSlices]

/-- **Every request of row `r` of a THR entry's groups** is a FILTER row (`r < |carriers|`) or the RADIX row
(`r = |carriers|`). -/
theorem thrGroups_rows (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (FP : GapParams) (e : GapSeed FP) (D : ListData) (g : ThrEq P Cs algorithm)
    (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (s : ZMod pr.val) (G row nw : ℕ) (Q : ℕ → RowReq → Prop)
    (hF : ∀ j, j < carriers.length → Q j (filtRow (thrSlices P Cs carriers) FP e G row nw j))
    (hR : Q carriers.length (radRow P Cs carriers algorithm den D g pr s G row nw)) (r : ℕ) :
    ∀ q ∈ (thrGroups P Cs carriers algorithm den FP e D g pr s G row nw).getD r [], Q r q := by
  intro q hq
  unfold thrGroups at hq
  by_cases hr : r < carriers.length
  · rw [List.getD_append _ _ _ _ (by simpa using hr), List.getD_eq_getElem _ _ (by simpa using hr)] at hq
    simp only [List.getElem_map, List.getElem_range, List.mem_singleton] at hq
    subst hq
    exact hF r hr
  · obtain ⟨k, rfl⟩ : ∃ k, r = carriers.length + k := ⟨r - carriers.length, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by simp)] at hq
    simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left] at hq
    rcases k with _ | k
    · simp only [List.getD_cons_zero, List.mem_singleton] at hq
      subst hq
      exact hR
    · rw [List.getD_eq_default _ _ (by simp)] at hq
      simp at hq

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- **Every request of row `r` of a THR entry** is a FILTER row (`r < |carriers|`) or the RADIX row
(`r = |carriers|`), at the entry's star row. -/
theorem thrGrp_rows (t row : ℕ) (Q : ℕ → RowReq → Prop)
    (hF : ∀ (e : GapSeed (I.filterParams .thr n)) (j : ℕ), j < carriers.length →
      Q j (filtRow (thrSlices (I.starParams n hs) Cs carriers) (I.filterParams .thr n) e
        (thrPool (I.starParams n hs) Cs carriers).length row n j))
    (hR : ∀ (g : ThrEq (I.starParams n hs) Cs alg)
      (pr : PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) (s : ZMod pr.val),
      Q carriers.length (radRow (I.starParams n hs) Cs carriers alg (thrCallDen alg I hs Cs)
        (thrCallD alg I hs Cs carriers translation) g pr s (thrPool (I.starParams n hs) Cs carriers).length row n))
    (r : ℕ) : ∀ q ∈ (thrGrp alg I hs Cs carriers translation t row).getD r [], Q r q := by
  intro q hq
  unfold thrGrp at hq
  split_ifs at hq with ht
  · exact thrGroups_rows (I.starParams n hs) Cs carriers alg (thrCallDen alg I hs Cs) _ _ _ _ _ _ _ row n Q
      (fun j hj => hF _ j hj) (hR _ _ _) r q hq
  · rcases getD_mem_or_nil (List.replicate (carriers.length + 1) ([] : List RowReq)) r with hm | hnil
    · rw [(List.mem_replicate.mp hm).2] at hq
      simp at hq
    · rw [hnil] at hq
      simp at hq

/-- Every THR row group has at most one request. -/
theorem thrGrp_mem_length (t row : ℕ) : ∀ g ∈ thrGrp alg I hs Cs carriers translation t row, g.length ≤ 1 := by
  intro g hg
  unfold thrGrp at hg
  split_ifs at hg
  · unfold thrGroups at hg
    rcases List.mem_append.mp hg with h1 | h2
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h1
      simp
    · rw [List.mem_singleton] at h2
      subst h2
      simp
  · rw [(List.mem_replicate.mp hg).2]
    simp

/-- **(1) Factor counts by row position.** -/
theorem thr_rows_factors : ∀ i r, r < carriers.length + 1 →
    SeedFix.Uniform ((thrExprs alg I hs Cs carriers translation).getD (i * (carriers.length + 1) + r) [])
      (if r < carriers.length then 1 else 2 * thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) := by
  intro i r hr
  unfold thrExprs thrBatchE
  refine rows_uniform _ _ _ (thrGrp alg I hs Cs carriers translation)
    (fun r => if r < carriers.length then 1 else 2 * thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))
    (fun t row => thrGrp_length alg I hs Cs carriers translation t row) ?_ i r hr
  intro t row r _ _ _ q hq
  refine thrGrp_rows alg I hs Cs carriers translation t row
    (fun r q => SeedFix.Uniform (refOf q) (if r < carriers.length then 1 else
      2 * thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))) ?_ ?_ r q hq
  · intro e j hj tm htm
    simp only [if_pos hj]
    unfold filtRow at htm
    rw [filt_ref, List.mem_singleton] at htm
    subst htm
    rfl
  · intro g pr s tm htm
    simp only [lt_irrefl, if_false]
    exact (radRow_ok _ _ _ _ _ _ g pr s row n tm htm).2.1

/-- The THR labels of FILTER slice `j < |carriers|` at star row `row < N²`. -/
theorem thr_labs_ok (row j N : ℕ) (hrow : row < N ^ 2) (hj : j < carriers.length) :
    LabsOk ((thrSlices (I.starParams n hs) Cs carriers).getD j []).length
      (CompilerMachine.Pool.labsOf (thrPool (I.starParams n hs) Cs carriers).length row
        (sliceGis (thrSlices (I.starParams n hs) Cs carriers) j))
      (4 * (N * N) * (thrPool (I.starParams n hs) Cs carriers).length) := by
  have h := labsOf_ok (thrPool (I.starParams n hs) Cs carriers).length row
    (sliceGis (thrSlices (I.starParams n hs) Cs carriers) j)
    ((thrSlices (I.starParams n hs) Cs carriers).getD j []).length (by rw [sliceGis_length])
    (fun gi hgi => mem_sliceGis_lt _ j (by rw [thrSlices_length]; exact Nat.lt_succ_of_lt hj) gi hgi)
  refine ⟨h.1, fun x hx => lt_of_lt_of_le (h.2 x hx) ?_⟩
  have : row + 1 ≤ N * N := by rw [← sq]; omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)

/-- **(2) Factors**: degree and atoms. -/
theorem thr_factors_ok : ∀ V ∈ thrExprs alg I hs Cs carriers translation, ∀ t ∈ V, ∀ p ∈ t.2,
    PolyOk (max (384 * (I.filterParams .thr n).walkLen + 1) (3 * listBound (thrCallD alg I hs Cs carriers translation)))
      (4 * (2 ^ SeedFix.callKh (I.starParams n hs) * 2 ^ SeedFix.callKh (I.starParams n hs)) *
        (thrPool (I.starParams n hs) Cs carriers).length) p := by
  unfold thrExprs
  apply terms_of_reqs (fun t => ∀ p ∈ t.2, PolyOk _ _ p)
  intro g hg q hq t ht p hp
  unfold thrBatchE at hg
  obtain ⟨tt, row, _, hrow, hg'⟩ := mem_batchOf hg
  obtain ⟨r, _, rfl⟩ := List.getElem_of_mem hg'
  rw [← List.getD_eq_getElem _ []] at hq
  refine thrGrp_rows alg I hs Cs carriers translation tt row (fun _ q => ∀ t ∈ refOf q, ∀ p ∈ t.2, PolyOk
    (max (384 * (I.filterParams .thr n).walkLen + 1) (3 * listBound (thrCallD alg I hs Cs carriers translation)))
    (4 * (2 ^ SeedFix.callKh (I.starParams n hs) * 2 ^ SeedFix.callKh (I.starParams n hs)) *
      (thrPool (I.starParams n hs) Cs carriers).length) p) ?_ ?_ r q hq t ht p hp
  · intro e j hj t' ht' p' hp'
    have hl := thr_labs_ok I hs Cs carriers row j _ hrow hj
    exact ((filtRow_ok _ _ _ _ _ _ _ _ hl t' ht').2.2 p' hp').mono (le_max_left _ _) le_rfl
  · intro g pr s t' ht' p' hp'
    have h := ((radRow_ok _ _ _ _ _ _ g pr s row n t' ht').2.2 p' hp')
    have hA : row + 1 ≤ 2 ^ SeedFix.callKh (I.starParams n hs) * 2 ^ SeedFix.callKh (I.starParams n hs) := by
      rw [← sq]; omega
    exact h.mono (le_max_right _ _) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA))

/-- **(3) Coefficients**: every THR term has coefficient `1`. -/
theorem thr_coef_one : ∀ V ∈ thrExprs alg I hs Cs carriers translation, ∀ t ∈ V, t.1 = 1 := by
  unfold thrExprs
  apply terms_of_reqs
  intro g hg q hq t ht
  unfold thrBatchE at hg
  obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
  obtain ⟨r, _, rfl⟩ := List.getElem_of_mem hg'
  rw [← List.getD_eq_getElem _ []] at hq
  refine thrGrp_rows alg I hs Cs carriers translation tt row (fun _ q => ∀ t ∈ refOf q, t.1 = 1) ?_ ?_ r q hq t ht
  · intro e j hj t' ht'
    unfold filtRow at ht'
    rw [filt_ref, List.mem_singleton] at ht'
    subst ht'
    rfl
  · intro g pr s t' ht'
    exact (radRow_ok _ _ _ _ _ _ g pr s row n t' ht').1

theorem one_le_sq_pow (M k : ℕ) : 1 ≤ ((M + 1) ^ 2) ^ k := Nat.one_le_pow _ _ (by positivity)

/-- Rows of at most one request each: the request's term count bounds the row's. -/
theorem rows_len_of_single (bl : List (List RowReq)) (T : ℕ) (h1 : ∀ g ∈ bl, g.length ≤ 1)
    (h2 : ∀ g ∈ bl, ∀ q ∈ g, (refOf q).length ≤ T) : ∀ V ∈ batchExprs bl, V.length ≤ T := by
  apply rows_length_le
  intro g hg
  have h := sum_map_le_card g (fun q => (refOf q).length) T (h2 g hg)
  calc _ ≤ _ := h
    _ ≤ 1 * T := Nat.mul_le_mul_right _ (h1 g hg)
    _ = T := Nat.one_mul _

/-- **(4) Term counts per row.** -/
theorem thr_row_terms_le : ∀ V ∈ thrExprs alg I hs Cs carriers translation,
    V.length ≤ (((thrCallD alg I hs Cs carriers translation).M + 1) ^ 2) ^
      thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) := by
  have hT := one_le_sq_pow (thrCallD alg I hs Cs carriers translation).M
    (thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs))
  unfold thrExprs
  refine rows_len_of_single _ _ ?_ ?_
  · intro g hg
    unfold thrBatchE at hg
    obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
    exact thrGrp_mem_length alg I hs Cs carriers translation tt row _ hg'
  · intro g hg q hq
    unfold thrBatchE at hg
    obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
    obtain ⟨r, _, rfl⟩ := List.getElem_of_mem hg'
    rw [← List.getD_eq_getElem _ []] at hq
    refine thrGrp_rows alg I hs Cs carriers translation tt row (fun _ q => (refOf q).length ≤
      (((thrCallD alg I hs Cs carriers translation).M + 1) ^ 2) ^
        thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) ?_ ?_ r q hq
    · intro e j hj
      exact hT
    · intro g pr s
      exact radRow_length _ _ _ _ _ _ g pr s _ row n

end ThrB

end NearCubicWires.WireExponent3_5.PrimAsm.BShape
