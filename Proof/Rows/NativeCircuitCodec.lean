import Proof.Rows.CircuitFlagRun

/-! The physical flag callback consumes exactly Production's native circuit
codec. All count and individual-gate width bounds follow from its byte cap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
namespace PCJ45bee56da9f34d5a_NativeCircuitCodec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.CompilerSemantics
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
open PCJ45bee56da9f34d5a_NativeGateLoop (word stream)
open PCJ45bee56da9f34d5a_FramedGateBank (strict)
noncomputable section

def thrGates {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :=
 List.ofFn (fun i=> (c.bottom (retainedTopIndex c i)).gate)
def thrTop {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :=thresholdWord (nonStrictAsStrict (retainedTopGate c))

end
end PCJ45bee56da9f34d5a_NativeCircuitCodec
