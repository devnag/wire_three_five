import Proof.CaseAnalysis.WitnessNativePolicy

/-! The native cache/policy continuation has exactly ten live initial
fields. All framing and source workspaces are physically fresh; the caller
aliases the already-produced counters and streams without copying them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
open LocalBitMultitape RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev tapes (a : PointwisePCPPAlgorithm) (D : ℕ):=base a+SourcePolicy.Call.extra D

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
