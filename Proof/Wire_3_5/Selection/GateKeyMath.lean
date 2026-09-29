import Proof.Wire_3_5.Selection.GateKeys

/-! # C1.4: the machine's key streams are the joins' key streams (P3:1339-1356)

Paper: "Enumerate each half's score vectors. For each of the sixteen corner patterns, count pairs" (P3:1344-1346).
C1.4's math (`gateJoin_tab`) writes a gate's row count through joins over the point tables `tabL`, `tabR`; the machine
writes, per join, the right points' keys then the left points' keys (`kw_spec`, in the routine's words `aW`, `aW'`).
This module identifies the two: the routine's words are the keys of the points (`ptR_keys`, `ptL_keys`), and each
join's machine stream is `keyStream W (A.map tagA ++ B.map tagB)` for the join's `A`, `B` (`kwYh_eq`, `kwYl_eq`,
`kwK1_eq`, `kwK3_eq`). Paper quantity: each join's key stream. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point

/-- A key stream is the framed words of its keys, then the end mark. -/
theorem keyStream_eq (W : ℕ) (hW : 1 ≤ W) (l : List ℕ) :
    keyStream W l = l.flatMap (fun x => frame (binary W x)) ++ [false] := by
  unfold keyStream StablePartition.stream StablePartition.recordsBits
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro x _
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  simp only [keyRec, binary, record, StablePartition.recordBits, frame]

variable (P : StarParams) (g : NormalizedThresholdGate P.n)

/-! ## The halves' ranges -/

theorem abs_halfR (y : ℕ) : |halfR P g y| ≤ ∑ i, |g.weight i| := by
  have h := accR P g 0 y
  have h1 := abs_partial (zAt (recsR P g)) y.testBit (rw P) (rw P) le_rfl
  have h2 := absSumR P g
  unfold accC at h; simp only [zero_add] at h
  rw [← h]; exact le_trans h1 h2

theorem abs_halfR' (y v : ℕ) : |halfR' P g y v| ≤ ∑ i, |g.weight i| := by
  have h := accR' P g 0 y v
  have h1 := abs_partial (zAt (recsR P g)) (fun p => xor (y.testBit p) (flipL P v p)) (rw P) (rw P) le_rfl
  have h2 := absSumR P g
  unfold accC at h; simp only [zero_add] at h
  rw [← h]; exact le_trans h1 h2

theorem abs_halfL (x : ℕ) : |halfL P g x| ≤ ∑ i, |g.weight i| := by
  have h := accL P g 0 x
  have h1 := abs_partial (zAt (recsL P g)) x.testBit (lw P) (lw P) le_rfl
  have h2 := absSumL P g
  unfold accC at h; simp only [zero_add, zero_sub] at h
  rw [show halfL P g x = -(((List.range (lw P)).map fun p => if x.testBit p then zAt (recsL P g) p else 0).sum) by
    rw [h]; ring, abs_neg]
  exact le_trans h1 h2

theorem abs_halfL' (x u : ℕ) : |halfL' P g x u| ≤ ∑ i, |g.weight i| := by
  have h := accL' P g 0 x u
  have h1 := abs_partial (zAt (recsL P g)) (fun p => xor (x.testBit p) (flipL P u p)) (lw P) (lw P) le_rfl
  have h2 := absSumL P g
  unfold accC at h; simp only [zero_add, zero_sub] at h
  rw [show halfL' P g x u = -(((List.range (lw P)).map fun p =>
    if xor (x.testBit p) (flipL P u p) then zAt (recsL P g) p else 0).sum) by rw [h]; ring, abs_neg]
  exact le_trans h1 h2

theorem natAbs_lt_of (z : ℤ) (V : ℕ) (h : |z| < 2 ^ V) : z.natAbs < 2 ^ V := by
  have : (z.natAbs : ℤ) < ((2 ^ V : ℕ) : ℤ) := by rw [Int.natCast_natAbs]; push_cast; exact h
  exact_mod_cast this

/-! ## The routine's words are the points' keys -/

theorem sum_lt' (V' : ℕ) (hK : KeyBound g V') : ∑ i, |g.weight i| < 2 ^ V' := by
  have := keyBound_int P g V' hK
  have := abs_nonneg g.threshold
  linarith

theorem theta_lt (V' : ℕ) (hK : KeyBound g V') : g.threshold.natAbs < 2 ^ V' := by
  have hk := keyBound_int P g V' hK
  have hnn : (0 : ℤ) ≤ ∑ i, |g.weight i| := Finset.sum_nonneg (fun i _ => abs_nonneg (g.weight i))
  exact natAbs_lt_of _ _ (by linarith)


section Keys
variable (V N : ℕ) (hKB : KeyBound g V)
include hKB

theorem ptR_keys (v y : ℕ) :
    aW P (recsR P g) (2 ^ V) 0 (fR P) N y =
      keyOf V (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).1 ∧
    aW' P (recsR P g) (2 ^ V) 0 (fR P) N v y =
      keyOf V (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).2 := by
  have hok : okB y.testBit P.b P.s 0 N (hh P) = true ↔ okR P N y := by
    rw [okB_iff P y N 0 (hh P) le_rfl]; unfold okR; simp only [Nat.zero_add]
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := size_facts P
  unfold aW aW'
  by_cases h : okR P N y
  · rw [if_pos (hok.mpr h), if_pos (hok.mpr h), if_pos h, h7, accR, accR']
    unfold keyOf RepairOrdinary.SignedSortKey.shifted
    constructor <;> (congr 1; push_cast; ring)
  · have h' : okB y.testBit P.b P.s 0 N (hh P) = false := Bool.eq_false_iff.mpr (fun h2 => h (hok.mp h2))
    simp only [h', Bool.false_eq_true, if_false, if_neg h]
    unfold keyOf RepairOrdinary.SignedSortKey.shifted
    have e : ((2 : ℤ) ^ V).toNat = 2 ^ V := by
      rw [show ((2 : ℤ) ^ V) = ((2 ^ V : ℕ) : ℤ) by push_cast; ring]; exact Int.toNat_natCast _
    simp [e]

theorem ptL_keys (u x : ℕ) :
    aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x =
      keyOf V (g.threshold - (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)).1) ∧
    aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x =
      keyOf V (g.threshold - (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)).2) := by
  have hok : okB x.testBit P.b P.s (hh P) N (hh P) = true ↔ okL P N x := by
    rw [okB_iff P x N (hh P) (hh P) le_rfl]; rfl
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := size_facts P
  have hθ : g.threshold.natAbs < 2 ^ V := theta_lt P g V hKB
  have hc := keyOf_cast V g.threshold hθ
  unfold aW aW'
  by_cases h : okL P N x
  · rw [if_pos (hok.mpr h), if_pos (hok.mpr h), if_pos h, h6, hc, accL, accL']
    unfold keyOf RepairOrdinary.SignedSortKey.shifted
    constructor <;> (congr 1; push_cast; ring)
  · have h' : okB x.testBit P.b P.s (hh P) N (hh P) = false := Bool.eq_false_iff.mpr (fun h2 => h (hok.mp h2))
    simp [h', if_neg h]

theorem ptR_minmax (v y : ℕ) :
    min (aW P (recsR P g) (2 ^ V) 0 (fR P) N y) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N v y) =
      keyOf V (min (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).1
        (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).2) ∧
    max (aW P (recsR P g) (2 ^ V) 0 (fR P) N y) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N v y) =
      keyOf V (max (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).1
        (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).2) := by
  obtain ⟨k1, k2⟩ := ptR_keys P g V N hKB v y
  have hs := sum_lt' P g V hKB
  have b1 : (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).1.natAbs < 2 ^ V := by
    split_ifs
    · exact natAbs_lt_of _ _ (lt_of_le_of_lt (abs_halfR P g y) hs)
    · simp
  have b2 : (if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)).2.natAbs < 2 ^ V := by
    split_ifs
    · exact natAbs_lt_of _ _ (lt_of_le_of_lt (abs_halfR' P g y v) hs)
    · simp
  rw [k1, k2]
  exact ⟨(keyOf_min V _ _ b1 b2).symm, (keyOf_max V _ _ b1 b2).symm⟩

theorem ptL_minmax (u x : ℕ) :
    min (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
        (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x) =
      keyOf V (loOf g.threshold (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0))) ∧
    max (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
        (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x) =
      keyOf V (hiOf g.threshold (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0))) := by
  obtain ⟨k1, k2⟩ := ptL_keys P g V N hKB u x
  have hk := keyBound_int P g V hKB
  have bd : ∀ z : ℤ, |z| ≤ ∑ i, |g.weight i| → (g.threshold - z).natAbs < 2 ^ V := fun z hz =>
    natAbs_lt_of _ _ (by have := abs_sub g.threshold z; linarith)
  have hz0 : |(0 : ℤ)| ≤ ∑ i, |g.weight i| := by
    simp only [abs_zero]; exact Finset.sum_nonneg (fun i _ => abs_nonneg (g.weight i))
  have b1 : (g.threshold - (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)).1).natAbs < 2 ^ V := by
    split_ifs
    · exact bd _ (abs_halfL P g x)
    · exact bd _ hz0
  have b2 : (g.threshold - (if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)).2).natAbs < 2 ^ V := by
    split_ifs
    · exact bd _ (abs_halfL' P g x u)
    · exact bd _ hz0
  rw [k1, k2]
  exact ⟨(keyOf_min V _ _ b1 b2).symm, (keyOf_max V _ _ b1 b2).symm⟩

/-- **The right table as the machine enumerates it.** -/
theorem tabR_eq (H : ℕ → ℕ → List Bool) :
    (tabR V (ptsR P g N)).flatMap (fun d => H d.1 d.2) =
      (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ rw P)).flatMap (fun x =>
        H (min (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))
          (max (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x)))) := by
  unfold tabR ptsR
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro v _
  rw [List.map_map, List.flatMap_map]
  apply List.flatMap_congr
  intro y _
  rw [(ptR_minmax P g V N hKB v y).1, (ptR_minmax P g V N hKB v y).2]
  rfl

/-- **The left table as the machine enumerates it.** -/
theorem tabL_eq (H : ℕ → ℕ → List Bool) :
    (tabL V g.threshold (ptsL P g N)).flatMap (fun d => H d.1 d.2) =
      (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ lw P)).flatMap (fun x =>
        H (min (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
            (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))
          (max (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
            (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x)))) := by
  unfold tabL ptsL
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro u _
  rw [List.map_map, List.flatMap_map]
  apply List.flatMap_congr
  intro x _
  rw [(ptL_minmax P g V N hKB u x).1, (ptL_minmax P g V N hKB u x).2]
  rfl

end Keys

/-! ## Each join's key stream -/

section Streams
variable (W V ℓ : ℕ) (T : List (ℕ × ℕ))

theorem innerY_stream : ((innerY T).map tagA).flatMap (fun x => frame (binary W x)) = T.flatMap (fun d => fYR W d.1 d.2) := by
  unfold innerY
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro d _
  simp [fYR, tagA]

theorem snd_stream : ((T.map Prod.snd).map tagB).flatMap (fun x => frame (binary W x)) =
    T.flatMap (fun d => fYLh W d.1 d.2) := by
  rw [List.map_map, List.flatMap_map]; rfl

theorem fst_stream : ((T.map Prod.fst).map tagB).flatMap (fun x => frame (binary W x)) =
    T.flatMap (fun d => fYLl W d.1 d.2) := by
  rw [List.map_map, List.flatMap_map]; rfl

theorem lvl2_stream : ((lvlK2 (V + 1) ℓ T).map tagA).flatMap (fun x => frame (binary W x)) =
    T.flatMap (fun d => fK2 W V ℓ d.1 d.2) := by
  unfold lvlK2
  rw [List.map_map, List.flatMap_map]
  apply List.flatMap_congr
  intro d _
  simp only [Function.comp, tagA, fK2, Bool.toNat_true]

theorem lvl1_stream : ((lvlK1 (V + 1) ℓ T).map tagB).flatMap (fun x => frame (binary W x)) =
    T.flatMap (fun d => fK1 W V ℓ d.1 d.2) := by
  unfold lvlK1
  rw [List.map_map, List.flatMap_map]
  apply List.flatMap_congr
  intro d _
  simp only [Function.comp, tagB, fK1, Bool.toNat_false, Nat.add_zero]

theorem lvl3_stream : ((lvlK3 (V + 1) ℓ T).map tagB).flatMap (fun x => frame (binary W x)) =
    T.flatMap (fun d => fK3 W V ℓ d.1 d.2) := by
  unfold lvlK3
  rw [List.map_map, List.flatMap_map]
  apply List.flatMap_congr
  intro d _
  simp only [Function.comp, tagB, fK3, Bool.toNat_false, Nat.add_zero]

end Streams

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
