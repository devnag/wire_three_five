import Proof.SourceAssembly.SourceRequestCurSide
import Proof.MachineModel.ClosureLocalSupport

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurPenalty
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceRequest.CurSide
open NearCubicWires.SourceFactorSel.Count (read_flag)
noncomputable section

/-! ## Helpers -/

/-- The right side's dock: `0 ↔ 96`, `1 ↔ 2`, `3 ↔ 4`. -/
def piR : Equiv.Perm (Fin 128) := Equiv.swap 0 96 * (Equiv.swap 1 2 * Equiv.swap 3 4)


/-! ## The machine -/

def slPL : Fin 10 → Fin 128 := ![1, 3, 80, 81, 82, 83, 84, 85, 86, 5]
def slPR : Fin 10 → Fin 128 := ![2, 4, 89, 90, 91, 92, 93, 94, 95, 5]
def t87 : Fin 5 → Fin 128 := ![86, 0, 87, 88, 5]
def s96 : Fin 9 → Fin 128 := ![0, 86, 96, 97, 98, 99, 100, 101, 5]
def t102 : Fin 5 → Fin 128 := ![95, 96, 102, 103, 5]

def endM := constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5

def rightM :=
  Composition.machine (RecoveryFocus.machine slPR SourceFactorSel.Count.side)
  (Composition.machine (subM s96) (Composition.machine (testM t102)
    (CloseoutRowsOriginalSwitch.machine endM (RecoveryFocus.machine piR (sideM true)) (102 : Fin 128))))

/-- **The penalty cursor** (ONE fixed machine on the common layout). -/
def penaltyM :=
  Composition.machine (RecoveryFocus.machine slPL SourceFactorSel.Count.side)
  (Composition.machine (testM t87) (CloseoutRowsOriginalSwitch.machine rightM (sideM false) (87 : Fin 128)))

/-! ## Its run -/

end
end NearCubicWires.SourceRequest.CurPenalty

