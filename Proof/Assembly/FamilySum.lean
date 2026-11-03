import Proof.MachineModel.TopDownPaidFamilySum

/-! The actual reusable family machine, complete source invariant, and
physical raw rewind/sum in a single fixed program. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9856d3e73b1d4df0_.FamilySum
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open RecoveryRootRound RecoveryExecution SignedSortKey
open RepairSource.CloseoutFinal.C10ExternalRowLoop CloseoutFinalC10RowAnswerWord
open P1TopDownPaidReusable (Datum Valid source outputSlot)
open RepairSource.VerifierDecoding
attribute [local irreducible] P1TopDownPaidReusable.machine CompetitorCrossScheduler.producer

noncomputable def raw (a : WilliamsAlgorithm) := (outputSlot a).castAdd 1
noncomputable def entry (a : WilliamsAlgorithm) (ds : List Datum) (S R B N : Nat) :=
  RepeatMachine.cfg 0 (source a ds S R B 0 []) N 1
noncomputable def after (a : WilliamsAlgorithm) (ds : List Datum) (S R B b : Nat) (xs : List Nat) :=
  RepeatMachine.cfg 3 (source a ds S R B xs.length (CompetitorCountFold.raw b xs)) xs.length 1
noncomputable def machine (a : WilliamsAlgorithm) :=
  Composition.machine (TapeEmbedding.machine 11 (familyWriter (P1TopDownPaidReusable.machine a)))
    (P1TopDownPaidFamilySum.machine (raw a))


end PCJ9856d3e73b1d4df0_.FamilySum
