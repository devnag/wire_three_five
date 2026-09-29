import Proof.CaseAnalysis.RecoveryCaseQuery

/-! The actual unconstrained case query reuses the whole compact-query
machine, retaining the original payload for the subsequent canonical search.
The capacity driver and all prepared fields are explicit caller obligations. -/
namespace NearCubicWires.RepairSource.CloseoutRecoveryCaseQuery
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
open SourceInterfaces OuterPCPRecovery CanonicalSATSelfReduction
open BoundedOracleStructuralCircuit RecoveryScheduleEnvelope
open RecoveryChoice RecoveryQuery RecoveryFormulaPrefix RecoveryOracle
open RecoveryQueryKernel
open private query_halted from Proof.Amplification.RecoveryPrefixBody
open private query_start_initial from Proof.Amplification.RecoveryPrefixBodyReady
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairSource.CloseoutRecoveryCaseQuery
