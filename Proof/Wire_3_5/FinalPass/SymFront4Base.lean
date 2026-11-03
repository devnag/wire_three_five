import Proof.Wire_3_5.FinalPass.SymFront3Base
import Proof.Wire_3_5.UnionMachine.NumsA13Base

/-! # The SYM front, part 4: the circuit count exported

`front_run` with the `numsBankG2` (the whole register export plus `dA = a'`, NumsA14) in place of `numsBankG`: the same
machine `frontM`, the exit **`FrontOutA`** = `FrontOut` plus `vA` (the circuit count `a'` in `dA`, register `321`), `vJ` (the base
list's `J = ⌈log₂B⌉ + 9` in `G 35`) and `vW` (the walk length in `G 39`), for the SYM numbers writer (`symNums`:
`a`, the flat tables' length). **`front_runA`**.

Paper quantity of the main type: the SYM call's tuple size `a` (P3:3170-3178, `symNums 0`) with the flat list
and the slices, in the bank. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g g_ne npow_le)
open NearCubicWires.SupplierPipeline

section Gate
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals)

/-- **The front's exit with the circuit count.** -/
structure FrontOutA {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (Pl : FlatListParams)
    (w : List Bool) (B : ℕ) (τ : St x) : Prop extends FrontOut x hx Cs Pl w B τ where
  vA : τ.val SymDec.dA = a'
  vJ : τ.val (SymDec.G 35) = Pl.base.J
  vW : τ.val (SymDec.G 39) = Pl.walkLen

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
