import Proof.Wire_3_5.Primitive.SeedFix.C4Geo

/-! # PA (d): the columns of `φ` as the writer emits them (value level for `C4Geo.colsField`)

P3:1212-1216 (star:partition): "Assign `r/2` whole blocks to each side. Each contributes exactly `b−s` free center bits
[...] A fixed linear basis of each code gives polynomial-time encoding and decoding"; the `C4Geo.cols` are
the basis vectors (the systematic basis of the Hamming code at the data positions, block by block) and the unit vectors
of the unblocked coordinates. This module rewrites the field `C4Geo.colsField P` into the word a streaming writer
emits:

* `binary_bitsValue` (the round trip `binary |l| (bitsValue l) = l`), **`colsField_eq`** (the marks of `natWord width`,
  then per column its bits as `[1,1,1,bit]` and `[1,0]`, then `0`);
* the column shapes: **`colBits_block`** (a block column: zeros, the codeword `cwWord i` of the data position
  `i = dpos (j mod (b−s))`, zeros) and **`colBits_unit`** (a unit column);
* the data positions: **`dataPos_length`** (`b − s` of them, `parCount`), **`dpos_flatMap`** (enumerating
  `dpos m`, `m < b−s`, = the positions `i < b` that are not parity positions);
* the codeword bits: **`cwBit_data`** (`[q = i]` off the parity positions), **`cwBit_par`** (bit `t` of `i+1` at the
  parity position `2^t − 1`);
* **`colsField_emit`**: the field as the writer emits it (`blkCol` per block and data position, `unitCol` per
  unblocked coordinate).

Paper quantity of the main types: the columns of `φ` (P3:1212-1216), in C3's column header `colsField`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoColsV
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)

theorem binary_bitsValue : ∀ l : List Bool, SignedSortKey.binary l.length (CanonicalBinary.bitsValue l) = l
  | [] => rfl
  | b :: l => by
    show ((CanonicalBinary.bitsValue (b :: l)) % 2 == 1) ::
      SignedSortKey.binary l.length (CanonicalBinary.bitsValue (b :: l) / 2) = b :: l
    simp only [CanonicalBinary.bitsValue]
    have h1 : (b.toNat + 2 * CanonicalBinary.bitsValue l) % 2 = b.toNat := by cases b <;> simp
    have h2 : (b.toNat + 2 * CanonicalBinary.bitsValue l) / 2 = CanonicalBinary.bitsValue l := by
      cases b <;> simp <;> omega
    rw [h1, h2, binary_bitsValue l]
    cases b <;> rfl

theorem frame_marksC (u : List Bool) : frame u = marks u ++ [false] := by
  have := RepairOrdinary.Streaming.frame_append u []
  simpa [RepairOrdinary.frame] using this

theorem marks_marks (l : List Bool) : marks (marks l) = l.flatMap fun b => [true, true, true, b] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [marks, List.flatMap_cons] at ih ⊢
    rw [← ih]
    simp [List.flatMap_cons]

theorem marks_flatMap {α : Type} (l : List α) (f : α → List Bool) : marks (l.flatMap f) = l.flatMap fun x => marks (f x) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.flatMap_cons, RepairOrdinary.Streaming.marks_append, ih]

/-- **The columns field, as a stream**: the marks of `natWord width`, then per column `j` its bits as `[1,1,1,bit]`
and the close `[1,0]`, then `0`. -/
theorem colsField_eq (P : StarParams) : PrimT.C4Geo.colsField P =
    marks (RepairRepresentation.natWord (PrimT.C4Geo.width P)) ++
      (List.range (PrimT.C4Geo.dRow P)).flatMap (fun j =>
        (PrimT.C4Geo.colBits P j).flatMap (fun b => [true, true, true, b]) ++ [true, false]) ++ [false] := by
  unfold PrimT.C4Geo.colsField MatrixScorePhi.columnsWord PrimT.C4Geo.cols
  rw [List.flatMap_map]
  have hc : ∀ j, frame (SignedSortKey.binary (PrimT.C4Geo.width P)
      (CanonicalBinary.bitsValue (PrimT.C4Geo.colBits P j))) = frame (PrimT.C4Geo.colBits P j) := by
    intro j
    have hl : (PrimT.C4Geo.colBits P j).length = PrimT.C4Geo.width P := by simp [PrimT.C4Geo.colBits]
    rw [← hl, binary_bitsValue]
  simp only [hc]
  rw [frame_marksC, RepairOrdinary.Streaming.marks_append, marks_flatMap]
  congr 2
  refine List.flatMap_congr fun j _ => ?_
  rw [frame_marksC, RepairOrdinary.Streaming.marks_append, marks_marks]
  rfl

/-! ## The column shapes -/

theorem ofFn_window (w a c : ℕ) (f : ℕ → Bool) (h : a + c ≤ w) :
    List.ofFn (fun p : Fin w => if a ≤ p.val ∧ p.val < a + c then f (p.val - a) else false) =
      List.replicate a false ++ List.ofFn (fun q : Fin c => f q.val) ++ List.replicate (w - a - c) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_append, List.length_replicate,
      List.getElem_replicate, List.length_ofFn]
    split_ifs <;> first | rfl | omega | (congr 1; omega) | simp_all

theorem b_posC (P : StarParams) : 0 < P.b := P.b_pos

/-- **A block column**: zeros, the Hamming codeword of the data position `dpos (j mod (b−s))` in block
`j / (b−s)`, zeros. -/
theorem colBits_block (P : StarParams) (j : ℕ) (hj : j < P.r / 2 * PrimT.C4Geo.dB P) :
    PrimT.C4Geo.colBits P j = List.replicate (j / PrimT.C4Geo.dB P * P.b) false ++
      List.ofFn (fun q : Fin P.b => PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P (j % PrimT.C4Geo.dB P)) q.val) ++
      List.replicate (PrimT.C4Geo.width P - j / PrimT.C4Geo.dB P * P.b - P.b) false := by
  have hb := b_posC P
  have hd : 0 < PrimT.C4Geo.dB P := by
    rcases Nat.eq_zero_or_pos (PrimT.C4Geo.dB P) with h0 | h0
    · rw [h0, Nat.mul_zero] at hj; omega
    · exact h0
  have hblk : j / PrimT.C4Geo.dB P < P.r / 2 := by rw [Nat.div_lt_iff_lt_mul hd]; exact hj
  have hle : j / PrimT.C4Geo.dB P * P.b + P.b ≤ PrimT.C4Geo.width P := by
    unfold PrimT.C4Geo.width
    have : (j / PrimT.C4Geo.dB P + 1) * P.b ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    omega
  rw [← ofFn_window _ _ _ _ hle]
  unfold PrimT.C4Geo.colBits
  congr 1
  funext p
  unfold PrimT.C4Geo.colBit
  rw [if_pos hj]
  set blk := j / PrimT.C4Geo.dB P with hblkd
  by_cases hp : blk * P.b ≤ p.val ∧ p.val < blk * P.b + P.b
  · rw [if_pos hp]
    have hdiv : p.val / P.b = blk := Nat.div_eq_of_lt_le hp.1 (by rw [Nat.succ_mul]; exact hp.2)
    have hmod : p.val % P.b = p.val - blk * P.b := by
      have := Nat.div_add_mod p.val P.b
      rw [hdiv] at this
      rw [Nat.mul_comm] at this
      omega
    have hA : p.val < P.r / 2 * P.b := by
      have : (blk + 1) * P.b ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at this
      omega
    simp [hA, hdiv, hmod]
  · rw [if_neg hp]
    have hne : p.val / P.b ≠ blk := by
      intro e
      apply hp
      constructor
      · rw [← e]; exact Nat.div_mul_le_self _ _
      · have := Nat.lt_div_mul_add (a := p.val) hb
        rw [e] at this
        omega
    simp [hne]

/-- **A unit column**: the unit vector of the unblocked coordinate `j − (r/2)(b−s)`. -/
theorem colBits_unit (P : StarParams) (j : ℕ) (hj1 : P.r / 2 * PrimT.C4Geo.dB P ≤ j) (hj2 : j < PrimT.C4Geo.dRow P) :
    PrimT.C4Geo.colBits P j = List.replicate (P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P)) false ++
      List.ofFn (fun _ : Fin 1 => true) ++
      List.replicate (PrimT.C4Geo.width P - (P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P)) - 1) false := by
  have hle : P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P) + 1 ≤ PrimT.C4Geo.width P := by
    unfold PrimT.C4Geo.dRow StarParams.leftCenterBits at hj2
    unfold PrimT.C4Geo.width PrimT.C4Geo.hL
    unfold PrimT.C4Geo.dB at hj1
    have : P.r / 2 * (P.b - P.s) ≤ P.r / 2 * P.b := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have he : P.r / 2 * PrimT.C4Geo.dB P = P.r / 2 * (P.b - P.s) := rfl
    omega
  rw [← ofFn_window _ _ _ (fun _ => true) hle]
  unfold PrimT.C4Geo.colBits
  congr 1
  funext p
  unfold PrimT.C4Geo.colBit
  rw [if_neg (by omega)]
  by_cases hp : P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P) ≤ p.val ∧
      p.val < P.r / 2 * P.b + (j - P.r / 2 * PrimT.C4Geo.dB P) + 1
  · rw [if_pos hp]; simp; omega
  · rw [if_neg hp]; simp; omega

/-! ## The data positions -/

theorem b_eqC (P : StarParams) : P.b = 2 ^ P.s - 1 := rfl

theorem pow_between (s t k : ℕ) (hk : k < 2 ^ s) (h : 2 ^ s + k = 2 ^ t) : k = 0 := by
  have h1 : 2 ^ s ≤ 2 ^ t := by omega
  have h2 : 2 ^ t < 2 ^ (s + 1) := by rw [Nat.pow_succ]; omega
  have hs1 : s ≤ t := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hs2 : t < s + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
  have : t = s := by omega
  subst this; omega

theorem singleHit (s S L : ℕ) (hs : s < S) (hL : L = 2 ^ s) :
    ((List.range L).filter (fun k => (List.range S).any fun t => 2 ^ s - 1 + k + 1 == 2 ^ t)).length = 1 := by
  have h1 := Nat.one_le_two_pow (n := s)
  rw [show L = 1 + (L - 1) by omega, List.range_add, List.filter_append, List.length_append]
  have hA : ((List.range 1).filter (fun k => (List.range S).any fun t => 2 ^ s - 1 + k + 1 == 2 ^ t)).length = 1 := by
    have : (List.range S).any (fun t => 2 ^ s - 1 + 0 + 1 == 2 ^ t) = true := by
      rw [List.any_eq_true]
      exact ⟨s, List.mem_range.2 hs, by simp; omega⟩
    simp [List.range_one, List.filter_cons, this]
  have hB : ((List.map (fun x => 1 + x) (List.range (L - 1))).filter
      (fun k => (List.range S).any fun t => 2 ^ s - 1 + k + 1 == 2 ^ t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Bool.not_eq_true, List.any_eq_false]
    intro t _
    simp only [beq_iff_eq, Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := pow_between s t (1 + k) (by omega) (by omega)
    omega
  rw [hA, hB]; rfl

theorem parCount (S : ℕ) : ∀ s, s ≤ S →
    ((List.range (2 ^ s - 1)).filter (fun i => (List.range S).any fun t => i + 1 == 2 ^ t)).length = s := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    have h1 := Nat.one_le_two_pow (n := s)
    have hsplit : 2 ^ (s + 1) - 1 = (2 ^ s - 1) + 2 ^ s := by rw [Nat.pow_succ]; omega
    rw [hsplit, List.range_add, List.filter_append, List.length_append, ih (by omega), List.filter_map,
      List.length_map]
    have := singleHit s S (2 ^ s) (by omega) rfl
    rw [show ((fun i => (List.range S).any fun t => i + 1 == 2 ^ t) ∘ fun x => 2 ^ s - 1 + x) =
      (fun k => (List.range S).any fun t => 2 ^ s - 1 + k + 1 == 2 ^ t) from rfl, this]

theorem isPar_iff (P : StarParams) (i : ℕ) (hi : i < P.b) :
    PrimT.C4Geo.isPar P i = true ↔ ∃ t, i + 1 = 2 ^ t := by
  unfold PrimT.C4Geo.isPar
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨t, -, h⟩; exact ⟨t, h⟩
  · rintro ⟨t, h⟩
    refine ⟨t, ?_, h⟩
    have hb := b_eqC P
    have : 2 ^ t < 2 ^ P.s := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this

/-- **The data positions number `b − s`.** -/
theorem dataPos_length (P : StarParams) : (PrimT.C4Geo.dataPos P).length = PrimT.C4Geo.dB P := by
  have h := List.length_eq_length_filter_add (l := List.range P.b) (fun i => PrimT.C4Geo.isPar P i)
  have hp : ((List.range P.b).filter (fun i => PrimT.C4Geo.isPar P i)).length = P.s :=
    parCount P.s P.s le_rfl
  rw [List.length_range, hp] at h
  unfold PrimT.C4Geo.dataPos PrimT.C4Geo.dB
  omega

theorem map_dpos (P : StarParams) :
    (List.range (PrimT.C4Geo.dB P)).map (PrimT.C4Geo.dpos P) = PrimT.C4Geo.dataPos P := by
  apply List.ext_getElem
  · simp [dataPos_length]
  · intro m h1 h2
    simp only [List.getElem_map, List.getElem_range, PrimT.C4Geo.dpos]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem filter_flatMapC {β : Type} (l : List ℕ) (p : ℕ → Bool) (f : ℕ → List β) :
    (l.filter p).flatMap f = l.flatMap (fun x => if p x then f x else []) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [List.filter_cons, h, ih]

/-- **The data positions, enumerated**: over `m < b − s`, `f (dpos m)` = over `i < b`, `f i` at the data positions. -/
theorem dpos_flatMap {β : Type} (P : StarParams) (f : ℕ → List β) :
    (List.range (PrimT.C4Geo.dB P)).flatMap (fun m => f (PrimT.C4Geo.dpos P m)) =
      (List.range P.b).flatMap (fun i => if PrimT.C4Geo.isPar P i then [] else f i) := by
  have e : (List.range (PrimT.C4Geo.dB P)).flatMap (fun m => f (PrimT.C4Geo.dpos P m)) =
      ((List.range (PrimT.C4Geo.dB P)).map (PrimT.C4Geo.dpos P)).flatMap f := by
    rw [List.flatMap_map]
  rw [e, map_dpos, PrimT.C4Geo.dataPos, filter_flatMapC]
  congr 1
  funext i
  cases PrimT.C4Geo.isPar P i <;> rfl

theorem range_mul_flatMapC {β : Type} (a b : ℕ) (f : ℕ → List β) :
    (List.range (a * b)).flatMap f = (List.range a).flatMap fun i => (List.range b).flatMap fun j => f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ, List.flatMap_append, List.flatMap_map]
    simp

/-! ## The codeword bits -/

/-- At a non-parity position the codeword bit is `[q = i]`. -/
theorem cwBit_data (P : StarParams) (i q : ℕ) (hq : ∀ t, q + 1 ≠ 2 ^ t) :
    PrimT.C4Geo.cwBit P i q = decide (q = i) := by
  unfold PrimT.C4Geo.cwBit
  have : ((List.range P.s).any fun t => (i + 1).testBit t && q + 1 == 2 ^ t) = false := by
    rw [List.any_eq_false]; intro t _; simp [hq t]
  rw [this, Bool.or_false]
  by_cases h : q = i <;> simp [h]

/-- At the parity position `2^t − 1` (not `i`) the codeword bit is bit `t` of `i + 1`. -/
theorem cwBit_par (P : StarParams) (i q t : ℕ) (ht : q + 1 = 2 ^ t) (hts : t < P.s) (hqi : q ≠ i) :
    PrimT.C4Geo.cwBit P i q = (i + 1).testBit t := by
  unfold PrimT.C4Geo.cwBit
  have hqi' : (q == i) = false := by simpa using hqi
  rw [hqi', Bool.false_or]
  cases h : (i + 1).testBit t
  · rw [List.any_eq_false]
    intro t' _
    have : q + 1 = 2 ^ t' → t' = t := by
      intro e; rw [ht] at e; exact (Nat.pow_right_injective (le_refl 2) e).symm
    by_cases e : q + 1 = 2 ^ t'
    · have := this e; subst this; simp [h]
    · simp [e]
  · rw [List.any_eq_true]
    exact ⟨t, List.mem_range.2 hts, by simp [h, ht]⟩

/-! ## The columns as the writer emits them -/

/-- One column bit as the writer emits it. -/
def e4 (b : Bool) : List Bool := [true, true, true, b]

/-- **A block column's word**: `pre` zeros, the codeword of data position `i`, `post` zeros, the column's end. -/
def blkCol (P : StarParams) (pre i post : ℕ) : List Bool :=
  (List.replicate pre false).flatMap e4 ++ (List.range P.b).flatMap (fun q => e4 (PrimT.C4Geo.cwBit P i q)) ++
    (List.replicate post false).flatMap e4 ++ [true, false]

/-- **A unit column's word**: `pre` zeros, a one, `post` zeros, the column's end. -/
def unitCol (pre post : ℕ) : List Bool :=
  (List.replicate pre false).flatMap e4 ++ e4 true ++ (List.replicate post false).flatMap e4 ++ [true, false]

theorem ofFn_rangeC {β : Type} (c : ℕ) (g : ℕ → β) : List.ofFn (fun q : Fin c => g q.val) = (List.range c).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

theorem dRow_eq (P : StarParams) :
    PrimT.C4Geo.dRow P = P.r / 2 * PrimT.C4Geo.dB P + PrimT.C4Geo.hL P := rfl

/-- **The columns field as the writer emits it**: the marks of `natWord width`; per block and per data position `i`
of the block, `blkCol`; per unblocked coordinate `u < h`, `unitCol`; then `0`. -/
theorem colsField_emit (P : StarParams) :
    PrimT.C4Geo.colsField P = marks (RepairRepresentation.natWord (PrimT.C4Geo.width P)) ++
      (List.range (P.r / 2)).flatMap (fun blk => (List.range P.b).flatMap (fun i =>
        if PrimT.C4Geo.isPar P i then [] else
          blkCol P (blk * P.b) i (PrimT.C4Geo.width P - blk * P.b - P.b))) ++
      (List.range (PrimT.C4Geo.hL P)).flatMap (fun u =>
        unitCol (P.r / 2 * P.b + u) (PrimT.C4Geo.width P - (P.r / 2 * P.b + u) - 1)) ++ [false] := by
  rw [colsField_eq, dRow_eq, List.range_add, List.flatMap_append, range_mul_flatMapC, List.flatMap_map]
  have hb := b_posC P
  have hB : ∀ blk ∈ List.range (P.r / 2),
      ((List.range (PrimT.C4Geo.dB P)).flatMap fun m =>
        (PrimT.C4Geo.colBits P (blk * PrimT.C4Geo.dB P + m)).flatMap (fun b => [true, true, true, b]) ++
          [true, false]) =
      (List.range P.b).flatMap (fun i => if PrimT.C4Geo.isPar P i then [] else
          blkCol P (blk * P.b) i (PrimT.C4Geo.width P - blk * P.b - P.b)) := by
    intro blk hblk
    rw [List.mem_range] at hblk
    rw [← dpos_flatMap P (fun i => blkCol P (blk * P.b) i (PrimT.C4Geo.width P - blk * P.b - P.b))]
    apply List.flatMap_congr
    intro m hm
    rw [List.mem_range] at hm
    have hj : blk * PrimT.C4Geo.dB P + m < P.r / 2 * PrimT.C4Geo.dB P := by
      have : (blk + 1) * PrimT.C4Geo.dB P ≤ P.r / 2 * PrimT.C4Geo.dB P := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at this; omega
    have hd : 0 < PrimT.C4Geo.dB P := by omega
    have hdiv : (blk * PrimT.C4Geo.dB P + m) / PrimT.C4Geo.dB P = blk := by
      rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt hm, Nat.add_zero]
    have hmod : (blk * PrimT.C4Geo.dB P + m) % PrimT.C4Geo.dB P = m := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hm]
    rw [colBits_block P _ hj, hdiv, hmod]
    unfold blkCol
    simp only [List.flatMap_append, ofFn_rangeC, List.flatMap_map, e4, List.append_assoc]
    rfl
  have hU : ∀ u ∈ List.range (PrimT.C4Geo.hL P),
      (PrimT.C4Geo.colBits P (P.r / 2 * PrimT.C4Geo.dB P + u)).flatMap (fun b => [true, true, true, b]) ++
          [true, false] =
      unitCol (P.r / 2 * P.b + u) (PrimT.C4Geo.width P - (P.r / 2 * P.b + u) - 1) := by
    intro u hu
    rw [List.mem_range] at hu
    rw [colBits_unit P _ (by omega) (by rw [dRow_eq]; omega)]
    rw [show P.r / 2 * PrimT.C4Geo.dB P + u - P.r / 2 * PrimT.C4Geo.dB P = u by omega]
    unfold unitCol
    simp [e4, List.append_assoc]
    rfl
  rw [List.flatMap_congr hB, List.flatMap_congr hU]
  simp only [List.append_assoc]

end NearCubicWires.WireExponent3_5.PrimAsm.GeoColsV
