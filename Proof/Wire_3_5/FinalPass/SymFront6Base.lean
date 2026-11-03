import Proof.Wire_3_5.FinalPass.SymFront4Base
import Proof.Wire_3_5.FinalPass.SymFront5Base

/-! # The SYM front, part 6: the exit with the empty slots' gate tables

`front_runA` over part 5's data stage (`dataPostW2`): the same machine `frontM`, the exit **`FrontOutB`** = `FrontOutA`
plus **`gates0`** (every gate-table tape past the tuple blank), for the SYM numbers writer's per-circuit width `tabH`
(`NumsA.tabHW_spec`: `gatesW (tabH G) G` or blank). **`front_runB`**.

Paper quantity of the main type: the SYM call's slices (the gate tables, blank past the tuple, P3:3049-3050) with the
flat list and the tuple size, in the bank. -/

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

/-- **The front's exit with the empty slots' gate tables.** -/
structure FrontOutB {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (Pl : FlatListParams)
    (w : List Bool) (B : ℕ) (τ : St x) : Prop extends FrontOutA x hx Cs Pl w B τ where
  gates0 : ∀ i : Fin 4, a' ≤ i.val → τ.st (tmapA x hx (DataDock.iSym i)) = []

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
