import Proof.Hierarchy.CompetitorWitnessCapSteps

/-! Cold whole-witness cap, with the rewind physically paid. The bound is
linear in the actual input length for every witness, including an overlong
one; only a true result licenses the subsequent nested decoder. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def guard := Rewind.machine machine

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
