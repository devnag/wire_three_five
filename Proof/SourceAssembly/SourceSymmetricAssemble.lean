import Proof.SourceAssembly.SourceSymmetricQuery

/- Assemble one native circuit from its physically produced count/TOP and
same-count native/support streams. All three copies are actual machine runs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ6e421fabe2aa4155_SourceSymmetricAssemble
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RecoveryRootRound RepairSource.VerifierDecoding
open CloseoutRowsTupleSeek (GatePair nativeWord supportWord)
noncomputable section



attribute [local irreducible] natWord CompareMachine.word PCPPQueryField.saved
  CloseoutRowsTupleSeek.nativeWord CloseoutRowsTupleSeek.supportWord





end
end PCJ6e421fabe2aa4155_SourceSymmetricAssemble
