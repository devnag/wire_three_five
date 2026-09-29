import Proof.Wire_3_5.Selection.GatePoint
import Proof.Wire_3_5.Selection.SortMath
import Proof.Wire_3_5.Selection.Math

/-! # C1.4 math: a gate's row counts from the machine's point tables (P3:1339-1358)

Paper: "Enumerate each half's score vectors. For each of the sixteen corner patterns, count pairs [...] Sum its exact
count" (P3:1344-1358). The machine writes, for each left point in its order, the ordered pair of keys
`(key lo, key hi)` (`tabL`), and for each right point the ordered pair `(key min(b,b'), key max(b,b'))` (`tabR`); every
join of C1.1's `gateJoin` reads these two tables. Proves **`gateRows_tab`**: a gate's row counts at the coset `N` are
`(J<(Y; hi) + 2Σ_ℓ J<(K2_ℓ; K1_ℓ)) − (J<(Y; lo) + 2Σ_ℓ J<(K2_ℓ; K3_ℓ))` over the tables, where the inner keys `Y` are
both keys of every right pair (`innerY`), and **`innerY_perm`** (the machine may write them pairwise). Paper quantity:
a gate's row counts at a coset. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math NearCubicWires.WireExponent3_5.SelectionMachine.Sort

variable (P : StarParams)

/-- The machine's left points at the coset `N` (null outside the coset). -/
def ptsL {n : ℕ} (g : NormalizedThresholdGate n) (N : ℕ) : List (ℤ × ℤ) :=
  (List.range (2 ^ (P.s * hh P))).flatMap fun u => (List.range (2 ^ lw P)).map fun x =>
    if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0)

/-- The machine's right points at the coset `N`. -/
def ptsR {n : ℕ} (g : NormalizedThresholdGate n) (N : ℕ) : List (ℤ × ℤ) :=
  (List.range (2 ^ (P.s * hh P))).flatMap fun v => (List.range (2 ^ rw P)).map fun y =>
    if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0)

/-- **The left table**: each left point's keys `(key lo, key hi)`. -/
def tabL (V : ℕ) (θ : ℤ) (L : List (ℤ × ℤ)) : List (ℕ × ℕ) := L.map fun p => (keyOf V (loOf θ p), keyOf V (hiOf θ p))

/-- **The right table**: each right point's keys `(key min, key max)`. -/
def tabR (V : ℕ) (R : List (ℤ × ℤ)) : List (ℕ × ℕ) := R.map fun q => (keyOf V (min q.1 q.2), keyOf V (max q.1 q.2))

/-- The inner keys of the 1-d joins, pair by pair. -/
def innerY (T : List (ℕ × ℕ)) : List ℕ := T.flatMap fun d => [d.1, d.2]

theorem gateRows_pts (g : NormalizedThresholdGate P.n) (N V : ℕ) (hV : KeyBound g V) :
    gateRows P (P.translationOfCodes (codesOfIdx P.s P.r N)) g = gateJoin V g.threshold (ptsL P g N) (ptsR P g N) := by
  rw [gateRows_eq_gateJoin P _ g (enumL P) (enumR P) (enumL_enumerates P) (enumR_enumerates P) V hV]
  congr 1
  · unfold enumL ptsL
    rw [List.map_flatMap]
    congr 1; funext u
    rw [List.map_map]
    congr 1; funext x
    exact ptLz_decode P g N u x
  · unfold enumR ptsR
    rw [List.map_flatMap]
    congr 1; funext v
    rw [List.map_map]
    congr 1; funext y
    exact ptRz_decode P g N v y

theorem keyOf_min (V : ℕ) (a b : ℤ) (ha : a.natAbs < 2 ^ V) (hb : b.natAbs < 2 ^ V) :
    keyOf V (min a b) = min (keyOf V a) (keyOf V b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left ((Joins.rKey V a b ha hb).2.2.mpr h)]
  · rw [min_eq_right h, min_eq_right ((Joins.rKey V b a hb ha).2.2.mpr h)]

theorem keyOf_max (V : ℕ) (a b : ℤ) (ha : a.natAbs < 2 ^ V) (hb : b.natAbs < 2 ^ V) :
    keyOf V (max a b) = max (keyOf V a) (keyOf V b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right ((Joins.rKey V a b ha hb).2.2.mpr h)]
  · rw [max_eq_left h, max_eq_left ((Joins.rKey V b a hb ha).2.2.mpr h)]

/-- The inner keys pair by pair are an arrangement of the right keys. -/
theorem innerY_perm (V : ℕ) (R : List (ℤ × ℤ)) (hR : ∀ q ∈ R, q.1.natAbs < 2 ^ V ∧ q.2.natAbs < 2 ^ V) :
    (innerY (tabR V R)).Perm (R.map (fun q => keyOf V q.1) ++ R.map (fun q => keyOf V q.2)) := by
  induction R with
  | nil => simp [innerY, tabR]
  | cons q R ih =>
    have hq := hR q List.mem_cons_self
    have ih' := ih (fun q' hq' => hR q' (List.mem_cons_of_mem _ hq'))
    simp only [innerY, tabR, List.map_cons, List.flatMap_cons, List.cons_append] at ih' ⊢
    rw [keyOf_min V _ _ hq.1 hq.2, keyOf_max V _ _ hq.1 hq.2]
    have hpair : [min (keyOf V q.1) (keyOf V q.2), max (keyOf V q.1) (keyOf V q.2)].Perm [keyOf V q.1, keyOf V q.2] := by
      rcases le_total (keyOf V q.1) (keyOf V q.2) with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h]; exact List.Perm.swap _ _ _
    have h3 : (keyOf V q.1 :: keyOf V q.2 :: (R.map (fun q => keyOf V q.1) ++ R.map (fun q => keyOf V q.2))).Perm
        (keyOf V q.1 :: (R.map (fun q => keyOf V q.1) ++ keyOf V q.2 :: R.map (fun q => keyOf V q.2))) :=
      List.Perm.cons _ List.perm_middle.symm
    have h12 := List.Perm.append hpair ih'
    exact h12.trans h3

/-- **`gateJoin` from the tables.** -/
theorem gateJoin_tab (V : ℕ) (θ : ℤ) (L R : List (ℤ × ℤ)) (hR : ∀ q ∈ R, q.1.natAbs < 2 ^ V ∧ q.2.natAbs < 2 ^ V) :
    gateJoin V θ L R =
      (joinLt (innerY (tabR V R)) ((tabL V θ L).map Prod.snd) + 2 * ((List.range (V + 1)).map fun ℓ =>
        joinLt (lvlK2 (V + 1) ℓ (tabR V R)) (lvlK1 (V + 1) ℓ (tabL V θ L))).sum) -
      (joinLt (innerY (tabR V R)) ((tabL V θ L).map Prod.fst) + 2 * ((List.range (V + 1)).map fun ℓ =>
        joinLt (lvlK2 (V + 1) ℓ (tabR V R)) (lvlK3 (V + 1) ℓ (tabL V θ L))).sum) := by
  unfold gateJoin joinPlus joinMinus
  have hp := innerY_perm V R hR
  rw [joinLt_perm hp (List.Perm.refl _), joinLt_perm hp (List.Perm.refl _)]
  simp only [tabL, tabR, List.map_map]
  rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
