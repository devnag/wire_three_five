import Proof.CaseAnalysis.RowsModeWindowLayout
import Proof.PCP.ProjectionNormalizationConstants

/-! The zero-population/zero-degree branch writes the exact constant raw
monomial body. This two-byte literal is part of the fixed ordinary program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowConstant
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 60:=fun _=>44
noncomputable def machine:=RecoveryFocus.machine slots (HierarchyFixedWord.raw [true,false])

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowConstant
