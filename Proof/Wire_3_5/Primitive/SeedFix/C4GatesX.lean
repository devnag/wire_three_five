import Proof.Wire_3_5.Primitive.SeedFix.C4GatesV

/-! # G1, the gate converter, part 7: the slots' tables in order (P3:1655-1664)

The pool of a call is its slots' gate lists in order (PA's `symSlices`/`thrSlices`: the carriers' doubled atoms,
then the circuits' bottoms). The converter runs the table loop on each listed slot (`tabsW js`); a blank or empty
table contributes nothing. **`tabsW_spec`**: the gate scratch receives `WS (js.flatMap Gs)` (every pool gate's native
word framed twice) and the count `|js.flatMap Gs|`.

Paper quantity of the main type: the pool's native words `WS (js.flatMap Gs)` in slot order. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

/-- The listed slots' tables in order. -/
def tabsW : List (Fin 6) → CW
  | [] => .skip
  | j :: js => .seq (tabW (tbl j)) (tabsW js)

theorem pairCost_mono {h H : ℕ} (hh : h ≤ H) : pairCost h ≤ pairCost H := by
  unfold pairCost; have := Nat.mul_le_mul hh hh; nlinarith

theorem gateCost_mono {h H : ℕ} (n : ℕ) (hh : h ≤ H) : gateCost h n ≤ gateCost H n := by
  unfold gateCost; have := pairCost_mono hh; have := Nat.mul_le_mul_left (n + 2) (Nat.add_le_add_right this 100)
  omega

theorem WS_append {n : ℕ} (A B : List (NormalizedThresholdGate n)) : WS (A ++ B) = WS A ++ WS B := by
  simp [WS, List.flatMap_append]

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
