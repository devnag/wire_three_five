import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyLayout

/-! The one selected source is physically executed on the literal hierarchy
input, then its original query/clause streams feed the complete cold PCP
recovery formula. No serialized intermediate or realization is supplied. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem request_positive (k CH Cpad : Nat) (code x : List Bool) (hpad : k+3≤Cpad) :
    1≤(HierarchyStreams.request k CH Cpad code x).1 := by
  have h:=(HierarchyPadding.linear_length k CH Cpad code x hpad).1
  change 1≤(HierarchyPadding.rawInput k CH Cpad code x).length
  omega

def normalized (k CH Cpad : Nat) (code x : List Bool) (hpad : k+3≤Cpad) :=
  (source.output (HierarchyStreams.request k CH Cpad code x)).normalized
    (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)
    (Dimensions.width_fits source _ (request_positive k CH Cpad code x hpad))
    (Dimensions.queries_fit source _ (request_positive k CH Cpad code x hpad))

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeHierarchy
