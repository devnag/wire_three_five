import Proof.SourceAssembly.SLoadMaskReady
import Proof.Assembly.AppendOutputLength

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.InputPass
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

variable (w : Nat)

def maskSlots (j : Fin (5 + w)) : Fin (22 + w) :=
  if j.val = 4 then ⟨0, by omega⟩ else ⟨17 + j.val, by omega⟩

def ret (k : Fin 4) : Fin (22 + w) := ⟨11 + k.val, by omega⟩
def retDrv : Fin (22 + w) := ⟨15, by omega⟩
def leadLog : Fin (22 + w) := ⟨16, by omega⟩
def drv : Fin (22 + w) := ⟨1, by omega⟩
def lenSlots (i : Fin 11) : Fin (22 + w) := ⟨i.val, by omega⟩

def machine (mask : MaskProducer) :=
  Composition.machine
    (SLoad.LeadDriver.machine (retDrv mask.work) (drv mask.work) (ret mask.work)
      (maskSlots mask.work) (leadLog mask.work))
    (Composition.machine (RecoveryFocus.machine (maskSlots mask.work) mask.machine)
      (RecoveryFocus.machine (lenSlots mask.work)
        (AppendOutputLength.machine SLoad.SuffixFrame.raw 7)))

section entryVals


end entryVals

def cost (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) : Nat :=
  SLoad.LeadDriver.prefixFuel a r + 1 +
    (maskBudget mask.coefficient mask.degree (maskData a r) + 1 +
      (2 * SLoad.RequestFrames.cost r.q r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length + 2))


end
end NearCubicWires.SourceRequest.InputPass
