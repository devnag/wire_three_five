import Proof.Wire_3_5.Selection.PointStep

/-! # C1.4: the point routine's quantities (P3:1339-1344)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342). The point routine walks one half's machine positions against a weight table; this module fixes what it
computes, as functions of the position count:
* `tbl W recs`: the weight table, each record `sign :: frame (binary W magnitude)` (`tbl_split`, `tbl_length`);
* `accC init z c P`: the running sum `init + Σ_{p<P} [c p]·z p` (`accC_succ`, `acc_step`);
* `synC c p0 j`: the running syndrome of a block, the xor of `i + 1` over the set bits `i < j` (`synC_succ`,
  `synC_lt`);
* the words' bits and segments: `binary_add`, `binary_mod`, `rd_frame_bit`, `frame_seg`.
Paper quantity: a half's integer score (the running sums) and a block's syndrome. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.Round (binary_succ)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (frameP_append)

/-! ## The weight table -/

/-- One weight record: the sign cell, then the framed magnitude. -/
def recBits (W : ℕ) (r : Bool × ℕ) : List Bool := r.1 :: frame (binary W r.2)

/-- **The weight table.** -/
def tbl (W : ℕ) (recs : List (Bool × ℕ)) : List Bool := recs.flatMap (recBits W)

theorem recBits_length (W : ℕ) (r : Bool × ℕ) : (recBits W r).length = 2 * W + 2 := by
  simp [recBits, frame_eq_frameP]

theorem tbl_length (W : ℕ) (recs : List (Bool × ℕ)) : (tbl W recs).length = recs.length * (2 * W + 2) := by
  induction recs with
  | nil => simp [tbl]
  | cons r rs ih =>
    simp only [tbl, List.flatMap_cons, List.length_append, recBits_length, List.length_cons] at ih ⊢
    rw [ih]; ring

/-- The record at position `p`. -/
def recAt (recs : List (Bool × ℕ)) (p : ℕ) : Bool × ℕ := recs.getD p (false, 0)

theorem tbl_split (W : ℕ) (recs : List (Bool × ℕ)) (p : ℕ) (hp : p < recs.length) :
    tbl W recs = tbl W (recs.take p) ++ ((recAt recs p).1 :: frame (binary W (recAt recs p).2)) ++
      tbl W (recs.drop (p + 1)) := by
  have e : recs = recs.take p ++ recAt recs p :: recs.drop (p + 1) := by
    unfold recAt
    rw [List.getD_eq_getElem _ _ hp, ← List.drop_eq_getElem_cons hp]
    exact (List.take_append_drop p recs).symm
  conv_lhs => rw [e]
  simp [tbl, recBits, List.flatMap_append]

/-- The signed value of the record at `p`. -/
def zAt (recs : List (Bool × ℕ)) (p : ℕ) : ℤ := sv (recAt recs p).1 (recAt recs p).2

/-! ## Running sums -/

/-- **The running sum** `init + Σ_{p<P} [c p]·z p`. -/
def accC (init : ℤ) (z : ℕ → ℤ) (c : ℕ → Bool) (P : ℕ) : ℤ :=
  init + ((List.range P).map fun p => if c p then z p else 0).sum

theorem accC_zero (init : ℤ) (z : ℕ → ℤ) (c : ℕ → Bool) : accC init z c 0 = init := by simp [accC]

theorem accC_succ (init : ℤ) (z : ℕ → ℤ) (c : ℕ → Bool) (P : ℕ) :
    accC init z c (P + 1) = accC init z c P + if c P then z P else 0 := by
  unfold accC
  rw [List.range_succ, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

/-- One step of a running sum on its natural value. -/
theorem acc_step (v : ℤ) (hv : 0 ≤ v) (b : Bool) (z : ℤ) :
    (if b then ((v.toNat : ℤ) + z).toNat else v.toNat) = (v + if b then z else 0).toNat := by
  cases b
  · simp
  · simp [Int.toNat_of_nonneg hv]

/-! ## Running syndromes -/

/-- **The running syndrome** of the block from `p0`: the xor of `i + 1` over the set bits `i < j`. -/
def synC (c : ℕ → Bool) (p0 j : ℕ) : ℕ :=
  (List.range j).foldl (fun y i => if c (p0 + i) then y ^^^ (i + 1) else y) 0

theorem synC_zero (c : ℕ → Bool) (p0 : ℕ) : synC c p0 0 = 0 := rfl

theorem synC_succ (c : ℕ → Bool) (p0 j : ℕ) :
    synC c p0 (j + 1) = if c (p0 + j) then synC c p0 j ^^^ (j + 1) else synC c p0 j := by
  unfold synC
  rw [List.range_succ, List.foldl_append]
  rfl

theorem synC_lt (c : ℕ → Bool) (p0 s : ℕ) : ∀ j, j < 2 ^ s → synC c p0 j < 2 ^ s
  | 0, _ => by rw [synC_zero]; exact Nat.two_pow_pos s
  | j + 1, hj => by
    rw [synC_succ]
    have ih := synC_lt c p0 s j (by omega)
    split_ifs
    · exact Nat.xor_lt_two_pow ih hj
    · exact ih

/-! ## Words: bits and segments -/

theorem binary_add : ∀ (a b x : ℕ), binary (a + b) x = binary a x ++ binary b (x / 2 ^ a)
  | 0, b, x => by simp [binary]
  | a + 1, b, x => by
    rw [show a + 1 + b = (a + b) + 1 by omega, binary_succ, binary_succ, binary_add a b (x / 2), Nat.div_div_eq_div_mul,
      pow_succ, Nat.mul_comm (2 ^ a) 2]
    rfl

theorem binary_mod : ∀ (a x : ℕ), binary a (x % 2 ^ a) = binary a x
  | 0, _ => rfl
  | a + 1, x => by
    rw [binary_succ, binary_succ, pow_succ', Nat.mod_mul_right_div_self, binary_mod a (x / 2), Nat.mod_mul_right_mod]

theorem binary_getD : ∀ (w x p : ℕ), p < w → (binary w x).getD p false = x.testBit p
  | 0, _, _, h => absurd h (by omega)
  | w + 1, x, 0, _ => by
    rw [binary_succ]
    simp only [List.getD_cons_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  | w + 1, x, p + 1, h => by
    rw [binary_succ, List.getD_cons_succ, binary_getD w (x / 2) p (by omega), Nat.testBit_div_two]

theorem frameP_getD_odd : ∀ (bs : List Bool) (p : ℕ), (frameP bs).getD (2 * p + 1) false = bs.getD p false
  | [], p => by simp
  | b :: bs, 0 => by simp
  | b :: bs, p + 1 => by
    rw [frameP_cons, show 2 * (p + 1) + 1 = (2 * p + 1) + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      frameP_getD_odd bs p, List.getD_cons_succ]

/-- The bit cell of position `p` of a framed word. -/
theorem rd_frame_bit (w x p : ℕ) (hp : p < w) : readTapeBit (frame (binary w x)) (2 * p + 1) = x.testBit p := by
  unfold readTapeBit
  rw [frame_eq_frameP, List.getD_append _ _ _ _ (by simp; omega), frameP_getD_odd, binary_getD w x p hp]

/-- **A segment of a framed word**: the `s` bits from bit `a` of a width-`w` word. -/
theorem frame_seg (w a s x : ℕ) (h : a + s ≤ w) :
    frame (binary w x) = frameP (binary a x) ++ frameP (binary s (x / 2 ^ a)) ++
      (frameP (binary (w - a - s) (x / 2 ^ a / 2 ^ s)) ++ [false]) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show a + s + c - a - s = c by omega, frame_eq_frameP, Nat.add_assoc, binary_add, binary_add, frameP_append,
    frameP_append]
  simp only [List.append_assoc]

/-- A segment compared with a number below `2^s`. -/
theorem binary_seg_eq (s y x : ℕ) (hy : y < 2 ^ s) : binary s y = binary s x ↔ y = x % 2 ^ s := by
  rw [← binary_mod s x]
  exact binary_inj s y (x % 2 ^ s) hy (Nat.mod_lt _ (Nat.two_pow_pos s))

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
