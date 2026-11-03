import Proof.CaseAnalysis.RowsOriginalMetadata
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomial
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.CaseAnalysis.RowsOriginalMonomial
import Proof.CaseAnalysis.RowsOriginalTemplates
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.CaseAnalysis.RowsProjectionReset
import Proof.CaseAnalysis.RowsRawAtomCache
import Proof.CaseAnalysis.RowsRawAtomLoop
import Proof.CaseAnalysis.WitnessFamilyRound
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.OrdinaryMatrixDimensionPrepare
import Proof.MachineModel.Semantics

/-! One concrete template writer, unit initializer, original-term product
loop, and metadata writer compose into a single ordinary program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalProducer
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsEstimator CloseoutRowsOriginalTemplates
open CloseoutRowsRawAtomSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def writerSlots : Fin 5→Fin 18:=![10,11,0,12,13]
def unitSlots : Fin 2→Fin 18:=![3,8]
def metaSlots (i : Fin 4) : Fin 18:=⟨i.val+14,by omega⟩
noncomputable def writer (r : Row):=RecoveryFocus.machine writerSlots (CloseoutRowsOriginalWriter.readyMachine r.factors)
noncomputable def unit:=RecoveryFocus.machine unitSlots SubstitutionAppend.unitMachine
noncomputable def inner:=TapeEmbedding.machine 8 CloseoutRowsOriginalMonomial.machine
noncomputable def metadata (r : Row):=RecoveryFocus.machine metaSlots (CloseoutRowsOriginalMetadata.machine r)
noncomputable def machine (r : Row):=Composition.machine (Composition.machine (Composition.machine (writer r) unit) inner) (metadata r)

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalProducer
