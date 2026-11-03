import Proof.SourceAssembly.SourceFactorSelDescF
import Proof.MachineModel.ClosureLocalSupport
import Proof.SourceAssembly.SourceRequestTermCompose
import Proof.SourceAssembly.SourceFactorSelCount

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Slot
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceFactorSel.Desc (Kind gdesc dT flagS flagO)
open NearCubicWires.SourceFactorSel.Count (read_flag wordM word0_step)
open NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## The reader's dock -/

/-- The reader's tape `k` in the slot universe: its five inputs and coefficient output on the slot's ports, every other tape
(its code and count outputs included) at `40 + k`. -/
def rdS (k : Fin 1081) : Fin 1121 :=
  if k.val = 0 then 8 else if k.val = 188 then 34 else if k.val = 191 then 35
  else if k.val = 383 then 9 else if k.val = 538 then 10 else if k.val = 1079 then 33
  else ⟨40 + k.val, by omega⟩


/-! ## The descriptor writer's docks -/

def descSl (b : Fin 1121) : Fin 27 → Fin 1121 :=
  ![0, 1, b, 575, 11, 12, 13, 14, 36, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]


def descM (b : Fin 1121) := RecoveryFocus.machine (descSl b) DescF.machine

/-! ## The machine -/

def termM := Composition.machine
  (CloseoutRowsOriginalSwitch.machine (wordM false (5 : Fin 1121) 34 16) (wordM false (4 : Fin 1121) 34 16) (2 : Fin 1121))
  (Composition.machine (wordM false (3 : Fin 1121) 35 16)
  (Composition.machine (RecoveryFocus.machine rdS SourceRequest.TermCompose.machine) (descM 6)))

def otherM := CloseoutRowsOriginalSwitch.machine (descM 7) (descM 6) (2 : Fin 1121)

/-- **One factor slot's pipeline** (ONE fixed machine, both modes). -/
def slotM := CloseoutRowsOriginalSwitch.machine termM otherM (1 : Fin 1121)

/-! ## The TERM branch -/

/-! ## The NOT-TERM branch (systematic or absent) -/

/-! ## The slot, mode-generic -/

/-- One cost bound for both branches (source polynomial). -/
def slotCost (wbits : List Bool) (jj idx cwid cw D : Nat) : Nat :=
  (2 * jj + 8 + 2) + 1 + ((2 * idx + 8) + 1 + (SourceRequest.TermCompose.readerCost wbits jj idx cwid cw + 1 +
    DescF.costF .orig D)) + 2 + (DescF.costF .sys D + DescF.costF .absent D + 4)

/-! ## Per mode (the consumer's descriptors) -/

section
open RepairRepresentation SupplierPipeline SourceInterfaces SupplierEstimator NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf thr_descAt sym_descAt)

end

end
end NearCubicWires.SourceFactorSel.Slot

