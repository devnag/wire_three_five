import Proof.Wire_3_5.Primitive.Writers.BShape5
import Proof.Wire_3_5.Primitive.Writers.PopCap

/-! # (P-b), the batch's shape, part 6: the rows' word lengths (`sym_word_le`, `bsz`)

A row's word (`exprWord`, the printer's record of its terms) is bounded from the shape: at most `T` terms, each with
coefficient `±1` and at most `W` factors, each factor at most `K` monomials of at most `D` atoms below `A` (atom codes
are unary, `|atomCode i| = i + 1`). An interpolated factor over `4L` corner positions has at most `(4L+1)^d`
monomials (`Print.goods_length_le`, P3:1484-1486).
* generic: `polyWord_le`, `termWord_le`, `exprWord_le`, `factorPoly_length_le`;
* **`sym_word_le`**, **`thr_word_le`** (the THR twin, `W = 2·digits + 1`): every SYM row's word is at most `T·(8 + w·((4G+1)^D·(2D(A+1)+2) + 2)) + 1`, with
  `T = (M+1)²·2^w`, `w` the walk length, `G = |symPool|`, `D` the degree bound of `sym_factors_ok`, `A` its atom bound.

Paper quantity of the main type: the SYM printed rows' encoding length (the words the enumeration reads, P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord termWord polyWord coefWord recW monoBits)

/-! ## Generic -/

theorem polyWord_le (p : Poly) (D A K : ℕ) (hK : p.length ≤ K) (hok : PolyOk D A p) :
    (polyWord p).length ≤ K * (2 * D * (A + 1) + 2) + 1 := by
  have hB : ∀ m ∈ p, (recW m).length ≤ 2 * D * (A + 1) + 2 := by
    intro m hm
    rw [ListMachine.Rec.recW_length]
    have h1 := PopCap.monoBits_length_le A m (fun i hi => Nat.le_of_lt ((hok m hm).2 i hi))
    have h2 : m.length * (A + 1) ≤ D * (A + 1) := Nat.mul_le_mul_right _ (hok m hm).1
    have : 2 * D * (A + 1) = 2 * (D * (A + 1)) := by ring
    omega
  unfold polyWord
  rw [List.length_append, List.length_singleton, List.length_flatMap]
  have hs := sum_map_le_card p (fun m => (recW m).length) _ hB
  have := Nat.mul_le_mul_right (2 * D * (A + 1) + 2) hK
  omega

theorem coefWord_pm1 (c : ℤ) (hc : c = 1 ∨ c = -1) : (coefWord c).length = 5 := by
  rcases hc with rfl | rfl <;> decide

theorem termWord_le (t : ℤ × List Poly) (W PW : ℕ) (hc : t.1 = 1 ∨ t.1 = -1) (hW : t.2.length ≤ W)
    (hp : ∀ p ∈ t.2, (polyWord p).length ≤ PW) : (termWord t).length ≤ W * (PW + 1) + 6 := by
  unfold termWord
  rw [List.length_append, coefWord_pm1 _ hc, List.length_append, List.length_singleton, List.length_flatMap]
  have hs := sum_map_le_card t.2 (fun f : List (List ℕ) => (polyWord f).length + 1) (PW + 1)
    (fun f hf => by have := hp f hf; omega)
  have := Nat.mul_le_mul_right (PW + 1) hW
  simp only [List.length_cons]
  omega

theorem exprWord_le (V : Expr) (T TW : ℕ) (hT : V.length ≤ T) (ht : ∀ t ∈ V, (termWord t).length ≤ TW) :
    (exprWord V).length ≤ T * (TW + 1) + 1 := by
  unfold exprWord
  rw [List.length_append, List.length_singleton, List.length_flatMap]
  have hs := sum_map_le_card V (fun t : ℤ × List (List (List ℕ)) => (termWord t).length + 1) (TW + 1)
    (fun t htm => by have := ht t htm; omega)
  have := Nat.mul_le_mul_right (TW + 1) hT
  simp only [List.length_cons]
  omega

theorem factorPoly_length_le (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) :
    (factorPoly f (4 * L) d labs).length ≤ (4 * L + 1) ^ d := by
  unfold factorPoly
  rw [List.length_map]
  calc (ListMachine.Interp.interpPrint f (4 * L) d).length ≤ (ListMachine.Interp.monos (4 * L) d).length :=
        List.length_filter_le _ _
    _ = (ListMachine.Interp.goods (4 * L) d).length := by
        rw [ListMachine.Interp.monos_eq_goods, List.length_map]
    _ ≤ (4 * L + 1) ^ d := ListMachine.Print.goods_length_le _ _

theorem factorPoly_length_le' (f : List Bool → Bool) (L d G D : ℕ) (labs : List ℕ) (hL : L ≤ G) (hd : d ≤ D) :
    (factorPoly f (4 * L) d labs).length ≤ (4 * G + 1) ^ D :=
  (factorPoly_length_le f L d labs).trans ((Nat.pow_le_pow_left (by omega) d).trans
    (Nat.pow_le_pow_right (by omega) hd))

theorem slice_length_le {α : Type} (sl : List (List α)) (j : ℕ) : (sl.getD j []).length ≤ sl.flatten.length := by
  by_cases hj : j < sl.length
  · have := sliceOff_add_le sl j hj; omega
  · rw [List.getD_eq_default _ _ (by omega)]; simp

/-! ## The SYM rows -/

section SymW
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

/-- Every factor of a SYM row has at most `(4G+1)^D` monomials, `G = |symPool|`, `D` the degree bound. -/
theorem sym_factor_count : ∀ V ∈ symExprs I hs Cs carriers, ∀ t ∈ V, ∀ p ∈ t.2,
    p.length ≤ (4 * (symPool Cs carriers).length + 1) ^
      max (384 * (I.filterParams .sym n).walkLen + 1) (3 * PopLink.lbP (symListParams I n a Cs carriers)) := by
  unfold symExprs
  apply terms_of_reqs (fun t => ∀ p ∈ t.2, p.length ≤ _)
  intro g hg q hq t ht p hp
  unfold symBatchE symBatch at hg
  obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
  rcases mem_symGroups hg' with ⟨j, hj, rfl⟩ | ⟨i, sgn, mm, t2, rfl⟩
  · rw [List.mem_singleton] at hq
    subst hq
    unfold filtRow at ht
    rw [filt_ref, List.mem_singleton] at ht
    subst ht
    rw [List.mem_singleton] at hp
    subst hp
    exact factorPoly_length_le' _ _ _ _ _ _ (slice_length_le _ j) (by rw [filtDeg_req]; exact le_max_left _ _)
  · obtain ⟨s, rfl⟩ := mem_popFactor hq
    rcases (mem_popRef _ t ht).2.2 p hp with rfl | ⟨s', qq, hqq, hpq⟩
    · simp only [List.length_singleton]
      exact Nat.one_le_pow _ _ (by omega)
    · unfold pairsC at hqq
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hqq
      rcases hpq with rfl | rfl <;>
      · exact factorPoly_length_le' _ _ _ _ _ _ (slice_length_le _ _)
          (by rw [PopLink.listBound_visit]; exact le_max_right _ _)

/-- **Every SYM row's word** (`sym_word_le`, `bsz`). -/
theorem sym_word_le : ∀ V ∈ symExprs I hs Cs carriers,
    (exprWord V).length ≤ ((symListParams I n a Cs carriers).M + 1) ^ 2 * 2 ^ (symListParams I n a Cs carriers).walkLen *
      ((symListParams I n a Cs carriers).walkLen * (((4 * (symPool Cs carriers).length + 1) ^
        max (384 * (I.filterParams .sym n).walkLen + 1) (3 * PopLink.lbP (symListParams I n a Cs carriers))) *
        (2 * max (384 * (I.filterParams .sym n).walkLen + 1) (3 * PopLink.lbP (symListParams I n a Cs carriers)) *
          (4 * (2 ^ SeedFix.callKh (I.starParams n hs) * 2 ^ SeedFix.callKh (I.starParams n hs)) *
            (symPool Cs carriers).length + 1) + 2) + 1 + 1) + 6 + 1) + 1 := by
  intro V hV
  apply exprWord_le V _ _ (sym_row_terms_le I hs Cs carriers V hV)
  intro t ht
  have hW : t.2.length ≤ (symListParams I n a Cs carriers).walkLen := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hV
    obtain ⟨q, hq, htq⟩ := mem_groupExpr.mp ht
    unfold symBatchE symBatch at hg
    obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
    rcases mem_symGroups hg' with ⟨j, hj, rfl⟩ | ⟨i, sgn, mm, t2, rfl⟩
    · rw [List.mem_singleton] at hq
      subst hq
      unfold filtRow at htq
      rw [filt_ref, List.mem_singleton] at htq
      subst htq
      simp only [List.length_singleton]
      unfold FlatListParams.walkLen
      omega
    · obtain ⟨s, rfl⟩ := mem_popFactor hq
      exact (mem_popRef _ t htq).2.1.le
  exact termWord_le t _ _ (sym_coef_pm1 I hs Cs carriers V hV t ht) hW (fun p hp =>
    polyWord_le p _ _ _ (sym_factor_count I hs Cs carriers V hV t ht p hp)
      (sym_factors_ok I hs Cs carriers V hV t ht p hp))

end SymW

/-! ## The THR rows -/

section ThrW
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPrime

theorem thrOccs_le (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) : (thrOccs P Cs).length ≤ (thrPool P Cs carriers).length := by
  have hj : carriers.length < (thrSlices P Cs carriers).length := by simp [thrSlices]
  have hsl : (thrSlices P Cs carriers).getD carriers.length [] = (thrOccs P Cs).map (·.gate) := by
    unfold thrSlices
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have h := sliceOff_add_le (thrSlices P Cs carriers) carriers.length hj
  rw [hsl, List.length_map] at h
  unfold thrPool
  omega

/-- A digit's population has at most one copy of each occurrence (binary digits). -/
theorem thrDigGis_length_le (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) :
    (thrDigGis P Cs carriers algorithm den g pr d).length ≤ (thrPool P Cs carriers).length := by
  unfold thrDigGis
  rw [List.length_flatMap]
  have hs := sum_map_le_card (List.finRange (thrOccs P Cs).length)
    (fun i => (List.replicate (digitOf (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val 2
      (thrDigits P Cs algorithm den) i d) (thrOff P Cs carriers + i)).length) 1 (fun i _ => by
        rw [List.length_replicate]; unfold digitOf; have := Nat.mod_lt
          (redCoeff (thrOccs P Cs) (thrRealize P Cs algorithm g) pr.val i / 2 ^ (d : ℕ)) (show 2 > 0 by norm_num)
        omega)
  rw [List.length_finRange, Nat.mul_one] at hs
  exact hs.trans (thrOccs_le P Cs carriers)

theorem thrDigs_L_le (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Carrier P.n)) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den)) (G row d : ℕ) :
    (digAt (thrDigs P Cs carriers algorithm den g pr G row) d).1 ≤ (thrPool P Cs carriers).length := by
  unfold digAt
  by_cases hd : d < (thrDigs P Cs carriers algorithm den g pr G row).length
  · rw [List.getD_eq_getElem _ _ hd]
    unfold thrDigs
    simp only [List.getElem_ofFn]
    exact thrDigGis_length_le P Cs carriers algorithm den g pr _
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- A RADIX digit print has at most `(4G+1)^{D'}` monomials. -/
theorem radP_length_le (D : ListData) (digs : List Dig) (d u G Dg : ℕ) (hL : (digAt digs d).1 ≤ G)
    (hd : 3 * listBound D ≤ Dg) :
    (radPp D digs d u).length ≤ (4 * G + 1) ^ Dg ∧ (radPm D digs d u).length ≤ (4 * G + 1) ^ Dg := by
  unfold radPp radPm polyC
  exact ⟨factorPoly_length_le' _ _ _ _ _ _ hL hd, factorPoly_length_le' _ _ _ _ _ _ hL hd⟩

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)

/-- Every factor of a THR row has at most `(4G+1)^D` monomials, `G = |thrPool|`, `D` the degree bound. -/
theorem thr_factor_count : ∀ V ∈ thrExprs alg I hs Cs carriers translation, ∀ t ∈ V, ∀ p ∈ t.2,
    p.length ≤ (4 * (thrPool (I.starParams n hs) Cs carriers).length + 1) ^
      max (384 * (I.filterParams .thr n).walkLen + 1) (3 * listBound (thrCallD alg I hs Cs carriers translation)) := by
  unfold thrExprs
  apply terms_of_reqs (fun t => ∀ p ∈ t.2, p.length ≤ _)
  intro g hg q hq t ht p hp
  unfold thrBatchE at hg
  obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
  obtain ⟨r, _, rfl⟩ := List.getElem_of_mem hg'
  rw [← List.getD_eq_getElem _ []] at hq
  refine thrGrp_rows alg I hs Cs carriers translation tt row (fun _ q => ∀ t ∈ refOf q, ∀ p ∈ t.2, p.length ≤
    (4 * (thrPool (I.starParams n hs) Cs carriers).length + 1) ^
      max (384 * (I.filterParams .thr n).walkLen + 1) (3 * listBound (thrCallD alg I hs Cs carriers translation)))
    ?_ ?_ r q hq t ht p hp
  · intro e j hj t' ht' p' hp'
    unfold filtRow at ht'
    rw [filt_ref, List.mem_singleton] at ht'
    subst ht'
    rw [List.mem_singleton] at hp'
    subst hp'
    exact factorPoly_length_le' _ _ _ _ _ _ (slice_length_le _ j) (by rw [filtDeg_req]; exact le_max_left _ _)
  · intro g pr s t' ht' p' hp'
    unfold radRow at ht'
    obtain ⟨d, u, hpt⟩ := (mem_radRef _ t' ht').2.2 p' hp'
    have hr := radP_length_le (thrCallD alg I hs Cs carriers translation)
      (thrDigs (I.starParams n hs) Cs carriers alg (thrCallDen alg I hs Cs) g pr
        (thrPool (I.starParams n hs) Cs carriers).length row) d u (thrPool (I.starParams n hs) Cs carriers).length
      (max (384 * (I.filterParams .thr n).walkLen + 1) (3 * listBound (thrCallD alg I hs Cs carriers translation)))
      (thrDigs_L_le _ _ _ _ _ g pr _ row d) (le_max_right _ _)
    rcases hpt with h | h
    · rw [h]; exact hr.1
    · rw [h]; exact hr.2

/-- **Every THR row's word** (the THR `bsz`). -/
theorem thr_word_le : ∀ V ∈ thrExprs alg I hs Cs carriers translation,
    (exprWord V).length ≤ (((thrCallD alg I hs Cs carriers translation).M + 1) ^ 2) ^
        thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) *
      ((2 * thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) + 1) *
        (((4 * (thrPool (I.starParams n hs) Cs carriers).length + 1) ^
          max (384 * (I.filterParams .thr n).walkLen + 1) (3 * listBound (thrCallD alg I hs Cs carriers translation))) *
          (2 * max (384 * (I.filterParams .thr n).walkLen + 1)
            (3 * listBound (thrCallD alg I hs Cs carriers translation)) *
            (4 * (2 ^ SeedFix.callKh (I.starParams n hs) * 2 ^ SeedFix.callKh (I.starParams n hs)) *
              (thrPool (I.starParams n hs) Cs carriers).length + 1) + 2) + 1 + 1) + 6 + 1) + 1 := by
  intro V hV
  apply exprWord_le V _ _ (thr_row_terms_le alg I hs Cs carriers translation V hV)
  intro t ht
  have hW : t.2.length ≤ 2 * thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) + 1 := by
    unfold thrExprs at hV
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hV
    obtain ⟨q, hq, htq⟩ := mem_groupExpr.mp ht
    unfold thrBatchE at hg
    obtain ⟨tt, row, _, _, hg'⟩ := mem_batchOf hg
    obtain ⟨r, _, rfl⟩ := List.getElem_of_mem hg'
    rw [← List.getD_eq_getElem _ []] at hq
    refine thrGrp_rows alg I hs Cs carriers translation tt row (fun _ q => ∀ t ∈ refOf q, t.2.length ≤
      2 * thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) + 1) ?_ ?_ r q hq t htq
    · intro e j hj t' ht'
      unfold filtRow at ht'
      rw [filt_ref, List.mem_singleton] at ht'
      subst ht'
      simp
    · intro g pr s t' ht'
      rw [(radRow_ok _ _ _ _ _ _ g pr s row n t' ht').2.1]
      omega
  exact termWord_le t _ _ (Or.inl (thr_coef_one alg I hs Cs carriers translation V hV t ht)) hW (fun p hp =>
    polyWord_le p _ _ _ (thr_factor_count alg I hs Cs carriers translation V hV t ht p hp)
      (thr_factors_ok alg I hs Cs carriers translation V hV t ht p hp))

end ThrW

end NearCubicWires.WireExponent3_5.PrimAsm.BShape
