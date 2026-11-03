import Proof.Wire_3_5.UnionMachine.PlanBase

/-! # C6: leaf U's enclosing application, the front at the refuter's witness length (F9)

The plan of `WireExponent3_5UnionMachinePlan` (M4) with ONE correction to its front residual: every per-witness field
of the front (`run`, `loop`, `capPos`, `accFit`, `sem`, `rej`, `len`, `perCall`, `capAcc`) is required only
at the refuter's witness length `w.length = N / 16` ("the weak machine guesses", P3:3669; base's weak machines read a
`⌊N/16⌋`-bit witness, `WitnessRun`). Over EVERY word the front is uninhabitable: its cost `cost N` depends on `N`
only, so it cannot read past `cost N` cells of the witness, while `decodeGuess` accepts a canonical guess word
followed by ANY number of zeros; two witnesses `encodeGuess g ++ 0^M` and `encodeGuess g ++ 0^{M-1} 1` (`M > cost N`)
run identically but have different meanings whenever `g` passes the slack check. The assembly only ever uses the
front at `List.ofFn w` with `w : BitInput (N/16)`, so the correction changes no other type: every other residual,
`WorkerAt`, `UnionLeafF` and the loop are those of M4.

Main statement: **`union_planW c1 dec frontsW count acc facts : ∀ l, UnionLeafF l`**. Paper quantity: `UnionLeafF l`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PlanW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-! ### Residual U0–U5, the front at the witness length -/

section Front

end Front


/-! ### The worker: front, loop, decision -/

section Assembly

end Assembly

/-! ### Layer B at the gate -/

section LeafB

end LeafB


end NearCubicWires.WireExponent3_5.UnionMachine.PlanW
