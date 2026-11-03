import Proof.SourceAssembly.SourceRequestCurPenalty

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
open NearCubicWires.SourceFactorSel.Count (read_flag)
noncomputable section

/-! ## Spec -/


/-- The multiplier of a clause record. -/
def g (c a b : Bool) : ℚ := (if c then -1 else 1) * ((if a then -1 else 1) * (if b then -1 else 1))

/-! ## One literal's part decode (local `Fin 14`) -/

def posL := Composition.machine (constM [true] (2 : Fin 14) 13) (copyM (0 : Fin 14) 3 13)
def neg1L := Composition.machine (subM (![0, 5, 3, 8, 9, 10, 11, 12, 13] : Fin 9 → Fin 14))
  (Composition.machine (constM [true] (2 : Fin 14) 13) (constM [true] (4 : Fin 14) 13))
def negL := Composition.machine (constM [true] (5 : Fin 14) 13)
  (Composition.machine (testM (![5, 0, 6, 7, 13] : Fin 5 → Fin 14))
    (CloseoutRowsOriginalSwitch.machine neg1L (CloseoutRowsOriginalSwitch.stop 14) (6 : Fin 14)))
/-- **One literal's part decode.** -/
def partL := CloseoutRowsOriginalSwitch.machine negL posL (1 : Fin 14)

/-! ## The tail: placement then multiplier (common layout; parts on `60/61/62` and `71/72/73`) -/

def placeW : Bool → Bool → Nat → Nat → List Wr
  | true, true, iL, iR => [.cp 61 9 iL, .c 7 [true], .cp 72 13 iR, .c 11 [true], .c 12 [true], .c 22 [true, true]]
  | true, false, iL, _ => [.cp 61 9 iL, .c 7 [true], .c 22 [true]]
  | false, true, _, iR => [.cp 72 9 iR, .c 7 [true], .c 8 [true], .c 22 [true]]
  | false, false, _, _ => []

def placeT := CloseoutRowsOriginalSwitch.machine (chainM ((placeW true true 0 0).map Wr.shape)).2
  (chainM ((placeW true false 0 0).map Wr.shape)).2 (71 : Fin 128)
def placeF := CloseoutRowsOriginalSwitch.machine (chainM ((placeW false true 0 0).map Wr.shape)).2
  (chainM ((placeW false false 0 0).map Wr.shape)).2 (71 : Fin 128)
def placeM := CloseoutRowsOriginalSwitch.machine placeT placeF (60 : Fin 128)

def rhoT (c : Bool) := CloseoutRowsOriginalSwitch.machine
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c true true)) 23 5)
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c true false)) 23 5) (73 : Fin 128)
def rhoF (c : Bool) := CloseoutRowsOriginalSwitch.machine
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c false true)) 23 5)
  (constM (CloseoutRowsEstimatorCoefficients.Product.record rhoW (g c false false)) 23 5) (73 : Fin 128)
def rhoM (c : Bool) := CloseoutRowsOriginalSwitch.machine (rhoT c) (rhoF c) (62 : Fin 128)

/-- **The clause tail** (placement, then the multiplier of cross flag `c`). -/
def tailM (c : Bool) := Composition.machine placeM (rhoM c)

end
end NearCubicWires.SourceRequest.CurClause

