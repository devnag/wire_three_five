import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorLayout

/-! Execute one actual factor, copy the new accumulator, and retire all
three temporary streams at their logical lengths. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine cacheMachine productMachine) accMachine) atomMachine) copyMachine) productClearMachine

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
