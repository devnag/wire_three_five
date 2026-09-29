import Proof.Amplification.RecoveryPCPFormulaResumeProofRun

/-! The physically recovered table is the same canonical accepted proof
used by the paper's Case-1 amplifier and hardness argument. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
open CanonicalSATSelfReduction OuterPCPRecovery RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem search_proof {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T)
    {n : Nat} (x : BitInput n) (complete : ∃ proof,∀ randomness,pcp.accepts x proof randomness) :
    RecoveryPrefixBody.search true (balancedCNFPayload (outerProofRecoveryFormula pcp x))
      (RecoveryFormulaPrefix.proofCount pcp n) []=
      List.ofFn (proofSelector pcp x complete).proof := by
  rw [RecoveryPrefixBody.search_canonical true (balancedCNFPayload (outerProofRecoveryFormula pcp x)) (outerProofRecoveryFormula pcp x) _
    (RecoveryFormulaPrefix.payload_decodes _) (outerProofRecoveryFormula_wellSized pcp x)
    (RecoveryFormulaPrefix.proof_range pcp x)]
  rw [proof_prefix pcp x complete (RecoveryFormulaPrefix.proofCount pcp n) (Nat.le_refl _)]
  rw [List.take_of_length_le (by simp [RecoveryFormulaPrefix.proofCount])]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
