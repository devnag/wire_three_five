import Proof.SourceAssembly.SourceFactorSelCoefAcc

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefBin
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc
noncomputable section

/-! ## Unary → framed binary at width `W` -/

/-- Local universe `Fin 16`: `0` `1^n` · `1` `1^W` · `2` output · `3` log · `4` copy · `5` zero summand ·
`6..14` the count's private tapes (its output word on `10`) · `15` the normalizer's flag. -/
def tobinM := Composition.machine (Count.sumM (0 : Fin 16) 5 4 3)
  (Composition.machine (RecoveryFocus.machine (![4, 6, 7, 8, 9, 10, 11, 12, 13, 14] : Fin 10 → Fin 16)
    CloseoutRowsCountBinary.machine)
  (RecoveryFocus.machine (![1, 10, 2, 15, 3] : Fin 5 → Fin 16) ClockNormalize.machine))

def tobinCost (n W : Nat) : Nat := (2 * (n + 0) + 6) + 1 + (CloseoutRowsCountBinary.budget n + 1 + (4 * W + 4))

/-! ## One switched factor slot -/

/-- The accumulator on the first thirty tapes of `Fin 32`. -/
def accIn : Fin 30 → Fin 32 := fun j => j.castAdd 2

/-- Skip branch: the factor is `1` — copy the three accumulators (zero summand on `31`). -/
def skipM := Composition.machine (Count.sumM (1 : Fin 32) 31 4 7)
  (Composition.machine (Count.sumM (2 : Fin 32) 31 5 7) (Count.sumM (3 : Fin 32) 31 6 7))

/-- Local universe `Fin 32`: `CoefAcc`'s thirty ports, `30` the slot's flag `[f]`, `31` a blank zero summand. -/
def accSwM := CloseoutRowsOriginalSwitch.machine (RecoveryFocus.machine accIn CoefAcc.accM) skipM (30 : Fin 32)

def skipCost (Na Da sa : Nat) : Nat := (2 * (Na + 0) + 6) + 1 + ((2 * (Da + 0) + 6) + 1 + (2 * (sa + 0) + 6))

def accSwCost (f s : Bool) (n d c Na Da sa : Nat) : Nat :=
  if f then CoefAcc.accCost s n d c Na Da sa + 2 else skipCost Na Da sa + 2

end
end NearCubicWires.SourceFactorSel.CoefBin

