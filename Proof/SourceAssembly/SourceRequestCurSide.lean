import Proof.SourceAssembly.SourceRequestCurWriter

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurSide
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceFactorSel.Count (mulM wordM mul_step word0_step read_flag)
noncomputable section

/-! ## Generic helpers: length bookkeeping, interval frames, the `CursorOut` builder -/

/-! ## The side contract -/

/-! ## The systematic side (`s = true`) -/

def sys0W (r : Bool) : List Wr :=
  [.c 6 [true], .c 8 [r], .c 22 [true], .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]
def sys1W (r : Bool) (y : Nat) : List Wr :=
  [.c 6 [true], .c 8 [r], .cp 27 13 y, .c 11 [true], .c 12 [r], .c 22 [true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (-1))]
def sys2W (r : Bool) (q u : Nat) : List Wr :=
  [.cp 42 9 q, .cp 43 13 u, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r], .c 22 [true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]

def t25 : Fin 5 → Fin 128 := ![24, 0, 25, 26, 5]
def s27 : Fin 9 → Fin 128 := ![0, 24, 27, 28, 29, 30, 31, 32, 5]
def t33 : Fin 5 → Fin 128 := ![1, 27, 33, 34, 5]
def s35 : Fin 9 → Fin 128 := ![27, 1, 35, 36, 37, 38, 39, 40, 5]
def d42 : Fin 11 → Fin 128 := ![35, 41, 42, 43, 44, 45, 46, 47, 48, 49, 5]

def sys2M (r : Bool) :=
  Composition.machine (subM s35) (Composition.machine (wordM false (1 : Fin 128) 41 5)
  (Composition.machine (divmodM d42) (chainM ((sys2W r 0 0).map Wr.shape)).2))

def sys12M (r : Bool) :=
  Composition.machine (subM s27) (Composition.machine (testM t33)
    (CloseoutRowsOriginalSwitch.machine (sys2M r) (chainM ((sys1W r 0).map Wr.shape)).2 (33 : Fin 128)))

/-- **The systematic side's decode.** -/
def sysM (r : Bool) :=
  Composition.machine (constM [true] (24 : Fin 128) 5) (Composition.machine (testM t25)
    (CloseoutRowsOriginalSwitch.machine (sys12M r) (chainM ((sys0W r).map Wr.shape)).2 (25 : Fin 128)))

/-! ## The auxiliary side (`s = false`) -/

def aux0W (r : Bool) (q u : Nat) : List Wr :=
  [.cp 28 9 q, .cp 29 13 u, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r], .c 22 [true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]
def aux1W (r : Bool) (a b c : Nat) : List Wr :=
  [.cp 53 9 a, .cp 54 13 b, .cp 46 17 c, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r], .c 15 [true], .c 16 [r],
    .c 22 [true, true, true], .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (-1))]
def aux2W (r : Bool) (a b c d : Nat) : List Wr :=
  [.cp 67 9 a, .cp 68 13 b, .cp 60 17 c, .cp 52 21 d, .c 7 [true], .c 8 [r], .c 11 [true], .c 12 [r],
    .c 15 [true], .c 16 [r], .c 19 [true], .c 20 [r], .c 22 [true, true, true, true],
    .c 23 (CloseoutRowsEstimatorCoefficients.Product.record rhoW (1 / 2))]

def t26 : Fin 5 → Fin 128 := ![25, 0, 26, 27, 5]
def d28 : Fin 11 → Fin 128 := ![0, 24, 28, 29, 30, 31, 32, 33, 34, 35, 5]
def s36 : Fin 9 → Fin 128 := ![0, 25, 36, 37, 38, 39, 40, 41, 5]
def t43 : Fin 5 → Fin 128 := ![42, 36, 43, 44, 5]
def d45 : Fin 11 → Fin 128 := ![36, 24, 45, 46, 47, 48, 49, 50, 51, 52, 5]
def d53 : Fin 11 → Fin 128 := ![45, 24, 53, 54, 55, 56, 57, 58, 59, 60, 5]
def s45 : Fin 9 → Fin 128 := ![36, 42, 45, 46, 47, 48, 49, 50, 5]
def d51 : Fin 11 → Fin 128 := ![45, 24, 51, 52, 53, 54, 55, 56, 57, 58, 5]
def d59 : Fin 11 → Fin 128 := ![51, 24, 59, 60, 61, 62, 63, 64, 65, 66, 5]
def d67 : Fin 11 → Fin 128 := ![59, 24, 67, 68, 69, 70, 71, 72, 73, 74, 5]

def aux0M (r : Bool) := Composition.machine (divmodM d28) (chainM ((aux0W r 0 0).map Wr.shape)).2
def aux1M (r : Bool) := Composition.machine (divmodM d45) (Composition.machine (divmodM d53)
  (chainM ((aux1W r 0 0 0).map Wr.shape)).2)
def aux2M (r : Bool) := Composition.machine (subM s45) (Composition.machine (divmodM d51)
  (Composition.machine (divmodM d59) (Composition.machine (divmodM d67) (chainM ((aux2W r 0 0 0 0).map Wr.shape)).2)))
def aux12M (r : Bool) := Composition.machine (subM s36) (Composition.machine (mulM (25 : Fin 128) 24 42 5)
  (Composition.machine (testM t43) (CloseoutRowsOriginalSwitch.machine (aux2M r) (aux1M r) (43 : Fin 128))))

/-- **The auxiliary side's decode.** -/
def auxM (r : Bool) :=
  Composition.machine (wordM false (1 : Fin 128) 24 5) (Composition.machine (mulM (1 : Fin 128) 24 25 5)
  (Composition.machine (testM t26) (CloseoutRowsOriginalSwitch.machine (aux12M r) (aux0M r) (26 : Fin 128))))

/-! ## One side: the aux flag selects the decode -/

/-- **Side `r`'s decode** (ONE fixed machine per side): aux flag `[!s]` on port `3`. -/
def sideM (r : Bool) := CloseoutRowsOriginalSwitch.machine (auxM r) (sysM r) (3 : Fin 128)

end
end NearCubicWires.SourceRequest.CurSide

