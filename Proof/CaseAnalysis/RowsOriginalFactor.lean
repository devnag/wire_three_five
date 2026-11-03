import Proof.CaseAnalysis.RowsOriginalCache
import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorRun

/-! One original family factor uses the actual single-cache reader and the
existing Cartesian product, accumulator copy, and logical-length cleanup. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFactor
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
open SubstitutionFactor (heads data productMachine accMachine atomMachine copyMachine productClearMachine)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def cacheMachine := RecoveryFocus.machine SubstitutionFactor.cacheSlots CloseoutRowsOriginalCache.machine
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine cacheMachine productMachine) accMachine) atomMachine) copyMachine) productClearMachine

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFactor
