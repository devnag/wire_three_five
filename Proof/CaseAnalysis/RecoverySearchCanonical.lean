import Proof.CaseAnalysis.RecoverySearchExecution

/-! The executed flag and descriptor have the original recovery meaning.
Canonical description order is supplied by the existing prefix theorem. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
open SourceInterfaces OuterPCPRecovery CanonicalSATSelfReduction CanonicalRecoveryLanguage
open BoundedOracleStructuralCircuit RecoveryScheduleEnvelope RecoveryChoice RecoveryFormulaPrefix
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_search {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (degree : Nat) {n : Nat} (x : BitInput n)
    (small : SmallOracle pcp degree x) :
    RecoveryPrefixBody.search true
      (payload (boundedOracleRecoveryFormula pcp x (oracleSizeBound degree (pcp.nativeWidth n))))
      (oracleCount pcp degree n) []=
    canonicalBoundedCircuitDescription (oracleSizeBound degree (pcp.nativeWidth n))
      (oracleSelector pcp degree x small).circuit := by
  rw [RecoveryPrefixBody.search_canonical true _ _ _ (payload_decodes _)
    (boundedOracleRecoveryFormula_wellSized pcp x _) (oracle_range pcp degree x)]
  rw [oracle_prefix pcp degree x small (oracleCount pcp degree n)
    (show oracleCount pcp degree n ≤ descriptionWidth (pcp.nativeWidth n)
      (oracleSizeBound degree (pcp.nativeWidth n)) from Nat.le_refl _)]
  rw [List.take_of_length_le (by rw [List.length_ofFn];exact Nat.le_refl _)]
  exact listOfFn_canonicalDescriptionInput _ _

end NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
