import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock
import Proof.CaseAnalysis.RowsEstimatorSubstitutionCopy
import Proof.CaseAnalysis.RowsEstimatorSubstitutionProduct

/-! One fixed accumulator bank for each source factor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) : Fin 10 → ℕ:=![pos,0,0,0,0,0,0,0,0,0]
def data (C : ℕ) (source cache atom acc product : List Bool) : Fin 10 → List Bool:=
  ![source,cache,ZeroPadding.pad C atom,ZeroPadding.pad C acc,ZeroPadding.pad C product,[false],
    List.replicate C false,List.replicate C false,List.replicate C false,List.replicate C false]
def cacheSlots : Fin 7 → Fin 10:=![0,1,2,5,6,7,8]
def productSlots : Fin 6 → Fin 10:=![3,2,4,6,7,8]
def accSlots : Fin 2 → Fin 10:=![3,8]
def atomSlots : Fin 2 → Fin 10:=![2,8]
def copySlots : Fin 6 → Fin 10:=![4,9,3,6,7,8]
def productClearSlots : Fin 2 → Fin 10:=![4,8]
noncomputable def cacheMachine:=RecoveryFocus.machine cacheSlots SubstitutionCache.machine
noncomputable def productMachine:=RecoveryFocus.machine productSlots SubstitutionProduct.machine
noncomputable def accMachine:=RecoveryFocus.machine accSlots SubstitutionErase.reset
noncomputable def atomMachine:=RecoveryFocus.machine atomSlots SubstitutionErase.reset
noncomputable def copyMachine:=RecoveryFocus.machine copySlots (SubstitutionCopy.machine true)
noncomputable def productClearMachine:=RecoveryFocus.machine productClearSlots SubstitutionErase.reset

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionFactor
