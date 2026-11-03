import Proof.CaseAnalysis.RowsOriginalWriterReady
import Proof.CaseAnalysis.RowsEstimatorSubstitutionAppend
import Proof.CaseAnalysis.RowsEstimatorCoefficientsProductRead

/-! Actual constant metadata for one of the finitely many paper templates.
The coefficient prefix is the consumer's width-three rational record. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMetadata
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution CloseoutRowsEstimator CloseoutRowsOriginalTemplates
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rho (r : Row):=CloseoutRowsEstimatorCoefficients.Product.record 3 r.rho
def count (r : Row):=CompareMachine.word r.factors.length
def parity (r : Row) : List Bool:=[r.parity.isSome,decide (r.parity=some 1)]
def rhoSlots : Fin 1→Fin 4:=fun _=>0
def countSlots : Fin 2→Fin 4:=![1,3]
def paritySlots : Fin 2→Fin 4:=![2,3]
noncomputable def writeRho (r : Row):=RecoveryFocus.machine rhoSlots (HierarchyFixedWord.raw (rho r))
noncomputable def writeCount (r : Row):=RecoveryFocus.machine countSlots (HierarchyFixedWord.machine (count r))
noncomputable def writeParity (r : Row):=RecoveryFocus.machine paritySlots (HierarchyFixedWord.machine (parity r))
def advance : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,![.stay,.right,.stay,.stay]⟩ else none
noncomputable def machine (r : Row):=Composition.machine
  (Composition.machine (Composition.machine (writeRho r) (writeCount r)) (writeParity r)) advance

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMetadata
