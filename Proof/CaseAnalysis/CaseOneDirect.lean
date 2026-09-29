import Proof.Amplification.RecoveryCaseOnePaddedBitInput
import Proof.CaseAnalysis.HierarchyRequestBound

/-! The common recovery program's direct Case1 worker. Genuine original
input produces the hierarchy request on the existing builder's output tape;
that tape is the original padded bit program's input. The requested address
is retained on its actual input port. No external wrapper is built or parsed. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOneDirect
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)




def budget {c d k target : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (H : OrdinaryHierarchy (fun n => n^(k + 2))) (Cpad : Nat) (hpad : k + 3 ≤ Cpad)
    (r : InputRequest)
    (hn : (RecoveryCaseOnePaddedBit.generated source amplifier H Cpad hpad r).arity ≤ target)
    (address : BitInput target) :=
  CloseoutHierarchyRequest.budget k H.coefficient (List.ofFn r.2) + 2 +
    RecoveryCaseOnePaddedBit.budget source amplifier H Cpad hpad r hn address

end
end NearCubicWires.RepairSource.CloseoutCaseOneDirect
