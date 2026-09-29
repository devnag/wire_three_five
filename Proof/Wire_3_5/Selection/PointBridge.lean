import Proof.Wire_3_5.Selection.PointLoop
import Proof.Wire_3_5.Selection.GateRef

/-! # C1.4: the point routine computes the paper's points (P3:1339-1344, 1195-1197)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342), for the halves whose blocks pass the coset's test (P3:1195-1197). The point routine (`pointR_spec`)
returns running sums over a weight table, a flip rule, and a syndrome test (`accC`, `okB`); this module identifies
them with C1.4's points (`halfL`, `halfL'`, `okL`, and the right versions) for the machine's weight tables: the left
table holds the weights negated (`recsL`), so the left words are the keys of `θ − a`; the right table holds the
weights (`recsR`). Main declarations: `recsL`, `recsR`, **`accL`**, **`accL'`**, **`accR`**, **`accR'`**, **`okB_iff`**,
**`flip_eq`**, **`acc_range`**. Paper quantity: a half's scores and its coset test, as the routine computes them. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.SelectionMachine.Math NearCubicWires.WireExponent3_5.SelectionMachine.Gate

variable (P : StarParams)

/-- **The left weight table**, in machine order, each weight negated. -/
def recsL (g : NormalizedThresholdGate P.n) : List (Bool × ℕ) :=
  (List.range (lw P)).map fun p => (!decide (wAt g (coordL P p) < 0), (wAt g (coordL P p)).natAbs)

/-- **The right weight table**, in machine order. -/
def recsR (g : NormalizedThresholdGate P.n) : List (Bool × ℕ) :=
  (List.range (rw P)).map fun p => (decide (wAt g (coordR P p) < 0), (wAt g (coordR P p)).natAbs)

theorem recsL_length (g : NormalizedThresholdGate P.n) : (recsL P g).length = lw P := by simp [recsL]

theorem recsR_length (g : NormalizedThresholdGate P.n) : (recsR P g).length = rw P := by simp [recsR]

theorem sv_neg (w : ℤ) : sv (!decide (w < 0)) w.natAbs = -w := by
  unfold sv
  by_cases h : w < 0
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    exact Int.ofNat_natAbs_of_nonpos (le_of_lt h)
  · simp only [h, decide_false, Bool.not_false, if_true]
    rw [Int.natAbs_of_nonneg (by omega)]

theorem sv_pos (w : ℤ) : sv (decide (w < 0)) w.natAbs = w := by
  unfold sv
  by_cases h : w < 0
  · simp only [h, decide_true, if_true]
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt h)]; ring
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    exact Int.natAbs_of_nonneg (by omega)

theorem zAt_recsL (g : NormalizedThresholdGate P.n) (p : ℕ) (hp : p < lw P) :
    zAt (recsL P g) p = -(wAt g (coordL P p)) := by
  unfold zAt recAt recsL
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]
  simp only [List.getElem_map, List.getElem_range]
  exact sv_neg _

theorem zAt_recsR (g : NormalizedThresholdGate P.n) (p : ℕ) (hp : p < rw P) :
    zAt (recsR P g) p = wAt g (coordR P p) := by
  unfold zAt recAt recsR
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]
  simp only [List.getElem_map, List.getElem_range]
  exact sv_pos _

theorem sum_neg_ite (c : ℕ → Bool) (w : ℕ → ℤ) : ∀ l : List ℕ,
    (l.map fun p => if c p then -(w p) else 0).sum = -(l.map fun p => w p * if c p then 1 else 0).sum
  | [] => by simp
  | p :: l => by
    simp only [List.map_cons, List.sum_cons, sum_neg_ite c w l]
    split_ifs <;> ring

theorem sum_ite (c : ℕ → Bool) (w : ℕ → ℤ) : ∀ l : List ℕ,
    (l.map fun p => if c p then w p else 0).sum = (l.map fun p => w p * if c p then 1 else 0).sum
  | [] => by simp
  | p :: l => by
    simp only [List.map_cons, List.sum_cons, sum_ite c w l]
    split_ifs <;> ring

/-- **The left word, unflipped**: `init − a`. -/
theorem accL (g : NormalizedThresholdGate P.n) (init : ℤ) (x : ℕ) :
    accC init (zAt (recsL P g)) x.testBit (lw P) = init - halfL P g x := by
  unfold accC halfL
  rw [List.map_congr_left (fun p hp => by rw [zAt_recsL P g p (List.mem_range.mp hp)]), sum_neg_ite]
  ring

/-- **The left word, flipped**: `init − a'`. -/
theorem accL' (g : NormalizedThresholdGate P.n) (init : ℤ) (x u : ℕ) :
    accC init (zAt (recsL P g)) (fun p => xor (x.testBit p) (flipL P u p)) (lw P) = init - halfL' P g x u := by
  unfold accC halfL'
  rw [List.map_congr_left (fun p hp => by rw [zAt_recsL P g p (List.mem_range.mp hp)]), sum_neg_ite]
  ring

/-- **The right word, unflipped**: `init + b`. -/
theorem accR (g : NormalizedThresholdGate P.n) (init : ℤ) (y : ℕ) :
    accC init (zAt (recsR P g)) y.testBit (rw P) = init + halfR P g y := by
  unfold accC halfR
  rw [List.map_congr_left (fun p hp => by rw [zAt_recsR P g p (List.mem_range.mp hp)]), sum_ite]

/-- **The right word, flipped**: `init + b'`. -/
theorem accR' (g : NormalizedThresholdGate P.n) (init : ℤ) (y v : ℕ) :
    accC init (zAt (recsR P g)) (fun p => xor (y.testBit p) (flipL P v p)) (rw P) = init + halfR' P g y v := by
  unfold accC halfR'
  rw [List.map_congr_left (fun p hp => by rw [zAt_recsR P g p (List.mem_range.mp hp)]), sum_ite]

/-! ## The coset test -/

theorem synC_testBit (c : ℕ → Bool) (p0 k : ℕ) : ∀ j,
    (synC c p0 j).testBit k = ((List.range j).map fun i => c (p0 + i) && (i + 1).testBit k).foldl xor false
  | 0 => by simp [synC_zero]
  | j + 1 => by
    rw [synC_succ, List.range_succ, List.map_append, List.foldl_append, ← synC_testBit c p0 k j]
    split_ifs with h
    · simp [Nat.testBit_xor, h]
    · simp [h]

theorem eq_iff_testBit_lt (s a b : ℕ) (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    a = b ↔ ∀ k < s, a.testBit k = b.testBit k := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < s
    · exact h k hk
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **The routine's coset test is the paper's**: every block's syndrome is the coset counter's segment `o + t`. -/
theorem okB_iff (x N o : ℕ) : ∀ t, t ≤ hh P →
    (okB x.testBit P.b P.s o N t = true ↔ ∀ t' < t, ∀ k < P.s, synBit P x t' k = N.testBit (P.s * (o + t') + k))
  | 0, _ => by simp [okB]
  | t + 1, ht => by
    have ih := okB_iff x N o t (by omega)
    have hb : P.b < 2 ^ P.s := by have := P.b_succ; omega
    have hsyn : synC x.testBit (t * P.b) P.b < 2 ^ P.s := synC_lt _ _ _ _ hb
    have hseg : N / 2 ^ (P.s * (o + t)) % 2 ^ P.s < 2 ^ P.s := Nat.mod_lt _ (Nat.two_pow_pos _)
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq, ih, eq_iff_testBit_lt P.s _ _ hsyn hseg]
    constructor
    · rintro ⟨h1, h2⟩ t' ht' k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with h | rfl
      · exact h1 t' h k hk
      · have := h2 k hk
        rw [synC_testBit] at this
        show ((List.range P.b).map fun i => x.testBit (t' * P.b + i) && (i + 1).testBit k).foldl xor false = _
        rw [this, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
        simp [hk, Nat.add_comm]
    · intro h
      refine ⟨fun t' ht' k hk => h t' (by omega) k hk, fun k hk => ?_⟩
      rw [synC_testBit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      have := h t (by omega) k hk
      simp only [synBit] at this
      rw [this]; simp [hk, Nat.add_comm]

/-- **The routine's flip is the paper's**: position `t·b + j` flips iff block `t`'s code is `j + 1`. -/
theorem flip_eq (u t j : ℕ) (ht : t < hh P) (hj : j < P.b) :
    decide (binary P.s (j + 1) = binary P.s (u / 2 ^ (P.s * t))) = flipL P u (t * P.b + j) := by
  have hb := P.b_succ
  have hdm := divmod t j P.b hj
  unfold flipL errCode
  rw [hdm.1, hdm.2]
  have e : P.s * (hh P - 1 - (hh P - 1 - t)) = P.s * t := by congr 1; omega
  rw [e]
  apply decide_eq_decide.mpr
  rw [binary_seg_eq P.s (j + 1) _ (by omega)]
  constructor
  · intro h; exact ⟨blk_lt t (hh P) j P.b ht hj, h.symm⟩
  · intro h; exact h.2.symm

theorem flip_free (u p : ℕ) (hp : hh P * P.b ≤ p) : flipL P u p = false := by
  unfold flipL; simp; omega

/-! ## The words' range -/

theorem abs_partial (z : ℕ → ℤ) (c : ℕ → Bool) (P n : ℕ) (hP : P ≤ n) :
    |((List.range P).map fun p => if c p then z p else 0).sum| ≤ ((List.range n).map fun p => |z p|).sum := by
  rw [listsum_range, listsum_range]
  calc |∑ p ∈ Finset.range P, (if c p then z p else 0)| ≤ ∑ p ∈ Finset.range P, |if c p then z p else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.range P, |z p| := Finset.sum_le_sum fun p _ => by split_ifs <;> simp
    _ ≤ ∑ p ∈ Finset.range n, |z p| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hP) (fun _ _ _ => abs_nonneg _)

theorem absSumL (g : NormalizedThresholdGate P.n) :
    ((List.range (lw P)).map fun p => |zAt (recsL P g) p|).sum ≤ ∑ i, |g.weight i| := by
  rw [List.map_congr_left (fun p hp => by rw [zAt_recsL P g p (List.mem_range.mp hp), abs_neg]), listsum_range]
  have h1 := sumL P (fun i => |g.weight i.1|)
  have h2 : ∑ p ∈ Finset.range (lw P), |wAt g (coordL P p)| =
      ∑ p ∈ Finset.range (lw P), (if hp : p < lw P then |g.weight ⟨coordL P p, coordL_lt P p hp⟩| else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    rw [dif_pos hp']; unfold wAt; rw [dif_pos (coordL_lt P p hp')]
  rw [h2, ← h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => P.centerSide i = true) (by simp) (fun i => |g.weight i|)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)

theorem absSumR (g : NormalizedThresholdGate P.n) :
    ((List.range (rw P)).map fun p => |zAt (recsR P g) p|).sum ≤ ∑ i, |g.weight i| := by
  rw [List.map_congr_left (fun p hp => by rw [zAt_recsR P g p (List.mem_range.mp hp)]), listsum_range]
  have h1 := sumR P (fun i => |g.weight i.1|)
  have h2 : ∑ p ∈ Finset.range (rw P), |wAt g (coordR P p)| =
      ∑ p ∈ Finset.range (rw P), (if hp : p < rw P then |g.weight ⟨coordR P p, coordR_lt P p hp⟩| else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_range.mp hp
    rw [dif_pos hp']; unfold wAt; rw [dif_pos (coordR_lt P p hp')]
  rw [h2, ← h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => ¬ P.centerSide i = true) (by simp) (fun i => |g.weight i|)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)

theorem keyBound_int (g : NormalizedThresholdGate P.n) (V : ℕ) (hK : KeyBound g V) :
    |g.threshold| + ∑ i, |g.weight i| < 2 ^ V := by
  unfold KeyBound at hK
  have : ((g.threshold.natAbs + ∑ i, (g.weight i).natAbs : ℕ) : ℤ) < ((2 ^ V : ℕ) : ℤ) := by exact_mod_cast hK
  push_cast at this
  simpa [Int.natCast_natAbs] using this

/-- **The left words stay in range**: every running sum from `θ + 2^V` lies in `[0, 2^(V+1))`. -/
theorem acc_rangeL (g : NormalizedThresholdGate P.n) (V : ℕ) (hK : KeyBound g V) (c : ℕ → Bool)
    (Pp : ℕ) (hP : Pp ≤ lw P) :
    0 ≤ accC (g.threshold + 2 ^ V) (zAt (recsL P g)) c Pp ∧
      accC (g.threshold + 2 ^ V) (zAt (recsL P g)) c Pp < 2 ^ (V + 1) := by
  have h1 := abs_partial (zAt (recsL P g)) c Pp (lw P) hP
  have h2 := absSumL P g
  have h3 := keyBound_int P g V hK
  have h5 : (2 : ℤ) ^ (V + 1) = 2 ^ V + 2 ^ V := by rw [pow_succ]; ring
  have ht := abs_nonneg g.threshold
  unfold accC
  constructor
  · have := neg_abs_le ((List.range Pp).map fun p => if c p then zAt (recsL P g) p else 0).sum
    have := neg_abs_le g.threshold
    linarith
  · have := le_abs_self ((List.range Pp).map fun p => if c p then zAt (recsL P g) p else 0).sum
    have := le_abs_self g.threshold
    linarith

/-- **The right words stay in range**: every running sum from `2^V` lies in `[0, 2^(V+1))`. -/
theorem acc_rangeR (g : NormalizedThresholdGate P.n) (V : ℕ) (hK : KeyBound g V) (c : ℕ → Bool)
    (Pp : ℕ) (hP : Pp ≤ rw P) :
    0 ≤ accC (2 ^ V) (zAt (recsR P g)) c Pp ∧ accC (2 ^ V) (zAt (recsR P g)) c Pp < 2 ^ (V + 1) := by
  have h1 := abs_partial (zAt (recsR P g)) c Pp (rw P) hP
  have h2 := absSumR P g
  have h3 := keyBound_int P g V hK
  have h5 : (2 : ℤ) ^ (V + 1) = 2 ^ V + 2 ^ V := by rw [pow_succ]; ring
  have ht := abs_nonneg g.threshold
  unfold accC
  constructor
  · have := neg_abs_le ((List.range Pp).map fun p => if c p then zAt (recsR P g) p else 0).sum
    linarith
  · have := le_abs_self ((List.range Pp).map fun p => if c p then zAt (recsR P g) p else 0).sum
    linarith

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
