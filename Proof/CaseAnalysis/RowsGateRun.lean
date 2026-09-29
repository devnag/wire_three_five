import Proof.CaseAnalysis.RowsGatePair
import Proof.CaseAnalysis.RowsGateTyped

/-! Original raw gate code to the complete framed native request. The
four canonical field verdicts guard the arithmetic call. On the same
decoded supported gate, its exact native request and support flag return
under one ordinary receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
open LocalBitMultitape RecoveryRootRound RecoveryExecution CloseoutRowsGateSupport
open SupplierPipeline CanonicalBinary CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def actualFirst : Machine 1035 CloseoutRowsGateColdStages.fieldStage.1 :=
  RecoveryFocus.machine oldSlots CloseoutRowsGateColdStages.fieldStage.2.val
noncomputable def actualLast (compressed : Bool) : Machine 1035 (CloseoutRowsGateColdStages.nativeStage compressed).1 :=
  RecoveryFocus.machine slots (CloseoutRowsGateColdStages.nativeStage compressed).2.val
noncomputable def actualMachine (compressed : Bool) :=
  CloseoutRowsGateColdPair.machine actualFirst (actualLast compressed) guard

end NearCubicWires.RepairOrdinary.CloseoutRowsGateCold
