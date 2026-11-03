import Proof.SourceAssembly.SourceRequestCurClausePart

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurClause
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceRequest.CurSide
open NearCubicWires.SourceFactorSel.Count (read_flag sumM wordM mulM sum_step word0_step mul_step flag_unary)
noncomputable section

/-! ## The machine -/

def sL0 : Fin 14 → Fin 128 := ![0, 3, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 5]
def sR28 : Fin 14 → Fin 128 := ![28, 4, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 5]
def sL46 : Fin 14 → Fin 128 := ![46, 3, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 5]
def sR47 : Fin 14 → Fin 128 := ![47, 4, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 5]
def tA : Fin 5 → Fin 128 := ![24, 0, 26, 27, 5]
def sY1 : Fin 9 → Fin 128 := ![0, 24, 28, 29, 30, 31, 32, 33, 5]
def tB : Fin 5 → Fin 128 := ![25, 28, 34, 35, 5]
def sY2 : Fin 9 → Fin 128 := ![28, 25, 36, 37, 38, 39, 40, 41, 5]
def tC : Fin 5 → Fin 128 := ![43, 36, 44, 45, 5]
def dX : Fin 11 → Fin 128 := ![36, 42, 46, 47, 48, 49, 50, 51, 52, 53, 5]

def litLM := Composition.machine (RecoveryFocus.machine sL0 partL) (tailM false)
def litRM := Composition.machine (RecoveryFocus.machine sR28 partL) (tailM false)
def endCM := constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5
def cross2M := Composition.machine (divmodM dX) (Composition.machine (RecoveryFocus.machine sL46 partL)
  (Composition.machine (RecoveryFocus.machine sR47 partL) (tailM true)))
def crossM := Composition.machine (subM sY2) (Composition.machine (wordM false (25 : Fin 128) 42 5)
  (Composition.machine (mulM (24 : Fin 128) 42 43 5) (Composition.machine (testM tC)
    (CloseoutRowsOriginalSwitch.machine endCM cross2M (44 : Fin 128)))))
def restM := Composition.machine (subM sY1) (Composition.machine (testM tB)
  (CloseoutRowsOriginalSwitch.machine crossM litRM (34 : Fin 128)))
/-- **The clause cursor** (ONE fixed machine on the common layout). -/
def clauseM := Composition.machine (sumM (1 : Fin 128) 3 24 5) (Composition.machine (sumM (2 : Fin 128) 4 25 5)
  (Composition.machine (testM tA) (CloseoutRowsOriginalSwitch.machine restM litLM (26 : Fin 128))))

/-! ## Sizes -/

/-! ## The left literal (`m < aL`) -/

/-! ## The right literal (`aL ≤ m`, `m - aL < aR`) -/

/-! ## The cross block (`y = m - aL - aR < aL·aR`) -/

/-! ## Blocks 2–end (`aL ≤ m`, `aR ≤ m - aL`) -/

end
end NearCubicWires.SourceRequest.CurClause

