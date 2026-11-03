import Proof.SourceAssembly.SourceRequestCurContract

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurMoment
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp
open NearCubicWires.SourceFactorSel.Count (mulM wordM mul_step word0_step read_flag)
noncomputable section

/-! ## The machine -/

def dmSl : Fin 11 → Fin 128 := ![0, 24, 9, 13, 28, 29, 30, 31, 32, 33, 5]
def tSl : Fin 5 → Fin 128 := ![25, 0, 26, 27, 5]

/-- Past the end: only the multiplier record `0`. -/
def endM := constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 0) (23 : Fin 128) 5

/-- Monomial `m < JL²`: the two digits, the two term flags, `k = 2`, multiplier `1`. -/
def bodyM :=
  Composition.machine (divmodM dmSl)
  (Composition.machine (constM [true] (7 : Fin 128) 5)
  (Composition.machine (constM [true] (11 : Fin 128) 5)
  (Composition.machine (constM [true, true] (22 : Fin 128) 5)
    (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW 1) (23 : Fin 128) 5))))

/-- **The moment cursor** (ONE fixed machine on the common layout). -/
def momentM :=
  Composition.machine (wordM false (1 : Fin 128) 24 5)
  (Composition.machine (mulM (1 : Fin 128) 24 25 5)
  (Composition.machine (testM tSl)
    (CloseoutRowsOriginalSwitch.machine endM bodyM (26 : Fin 128))))

/-! ## Its run -/

end

end NearCubicWires.SourceRequest.CurMoment

