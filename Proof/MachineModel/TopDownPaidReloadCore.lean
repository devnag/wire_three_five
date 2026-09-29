import Proof.MachineModel.TopDownPaidRetiredPayload

/-! The paid scanner/driver/count/retirement chain from literal cold words.
The native header and metadata are inputs; neither D nor a computed table is.
This is the row worker to be loaded from the physical sequential source. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReloadCore
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open CompetitorCrossScheduler (producer)
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine
  Paid.driver Paid.warm Paid.retire Paid.retiredMachine RawRowJoin.machine

noncomputable def bank (a : WilliamsAlgorithm) (A : Fin 64→List Bool)
    (C : Nat) (fields : Fin 7→List Bool) : Fin (tapes a)→List Bool :=
  Fin.addCases
    (WarmPrepare.data (producer a)
      (Fin.addCases (Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) A (Scanned.extra C))
        (fun _ : Fin (CloseoutRowsRawRecord.tapes (producer a))=>[])) 0 0 fields)
    (fun _ : Fin (ScannedClean.tapes a)=>[])
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  bank a (Prepare.input row) C (WarmFields.words row Q estimate 1 select)
noncomputable def scanSlots (a : WilliamsAlgorithm) (i : Fin 64) : Fin (tapes a) :=
  Paid.old a (producer a) (WarmPrepare.old (producer a)
    ((i.castAdd 6).castAdd (CloseoutRowsRawRecord.tapes (producer a))))
noncomputable def scanner (a : WilliamsAlgorithm) := RecoveryFocus.machine (scanSlots a) Prepare.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (scanner a) (Paid.retiredMachine a)
noncomputable def fuel (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat) :=
  Prepare.budget row+1+P1TopDownPaidRetiredPayload.fuel a row C Q
noncomputable def rawMachine (a : WilliamsAlgorithm) := RawRowJoin.machine (machine a) (port a)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B : Nat) :=
  RawRowJoin.budget (fuel a row C Q) (scalarWidth (EquationRow.request row) Q) B

end NearCubicWires.P1TopDownPaidReloadCore
