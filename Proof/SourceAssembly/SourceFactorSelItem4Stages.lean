import Proof.SourceAssembly.SourceRequestInput
import Proof.MachineModel.OrdinaryMatrixTemplateCopy
import Proof.Assembly.ClosureBinaryCacheMeasure

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Item4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-! ## LM: lead ; mask ; frame, on `Fin (9 + (5 + w))` -/

section lm
variable (w : Nat)

/-- `0` retDrv · `1` drv · `2..5` ret · `6` lead log · `7` target · `8` framer log · `9 + j` mask worker tape `j`. -/
def lmRet (i : Fin 4) : Fin (9 + (5 + w)) := ⟨2 + i.val, by omega⟩
def lmMask (j : Fin (5 + w)) : Fin (9 + (5 + w)) := ⟨9 + j.val, by omega⟩

def lmM (mask : MaskProducer) :=
  Composition.machine
    (SLoad.LeadDriver.machine (⟨0, by omega⟩ : Fin (9 + (5 + mask.work))) ⟨1, by omega⟩ (lmRet mask.work)
      (lmMask mask.work) ⟨6, by omega⟩)
    (Composition.machine (RecoveryFocus.machine (lmMask mask.work) mask.machine)
      (SLoad.MaskFrame.machine (lmMask mask.work ⟨4, by omega⟩) (⟨1, by omega⟩ : Fin (9 + (5 + mask.work)))
        ⟨7, by omega⟩ ⟨8, by omega⟩))

def lmCost (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) : Nat :=
  SLoad.LeadDriver.prefixFuel a r + 1 +
    (maskBudget mask.coefficient mask.degree (maskData a r) + 1 + (4 * r.q + 4))

/-! ## TK: the K template, copied (`MatrixTemplateCopy` under `Rewind`) -/

/-- The template copier with its heads rewound (`Fin 5`: `0` source template, `1, 2` unary scratch, `3` the copy, `4` rewind log). -/
def tkM := Rewind.machine MatrixTemplateCopy.machine

end lm

end
end NearCubicWires.SourceFactorSel.Item4

