import Proof.Wire_3_5.Primitive.SeedFix.C4SM

/-! # C4 per-call setup (item 3), part 14: **the SYM setup, docked**

P3:3011-3016, 2929-2941, 1886-1906, 3034-3037: before the seed-prefix loop of a SYM call, the stage writes, from the
framed request `natWord n ++ sfx` on its port `0` (the SYM batch word on port `1` untouched), the thirty-nine words of
the enumeration's rulers and constants, the generator's inputs and the compiler request's numbers (the numbers
program's exit words `wd`), the field's modulus word twice (`frame (binary ℓ (firstPrimitive ℓ))`: the enumeration's
constant and the finisher's input), the printer child's mask `1^{2^{d₂}}`, the loop's driver `1^{2^ρ}`, the compiler
request's fields `frame pre`, `frame post`, the loop's cells as `2^ρ` falses and its log as `2^ρ + 1` falses; the
finisher's region stays blank.

* `setupM` (the front, the numbers, the tail, base `SelectedErase`), `setupCost`, **`setup_run`**.

Paper quantities of the main type: the loop's entry words and the finisher's inputs on their tapes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

namespace Lay
variable (L : Lay)

theorem maskLP_false (i : Fin L.N) (h : i.val < L.oLP) : L.maskLP i = false := by
  unfold maskLP
  simp only [decide_eq_false_iff_not, not_and, not_lt]
  intro h'
  omega

end Lay

end NearCubicWires.WireExponent3_5.PrimT.C4Set
