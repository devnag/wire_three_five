import Proof.SourceAssembly.SourceFactorSelCoefPrim

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefAcc
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim
noncomputable section

/-! ## Docking with explicit exit vectors -/

/-! ## The record parse: three `FrameLoad`s, then `Rewind` -/

def fl (k : Fin 5) : Machine 5 4 := RecoveryFocus.machine (![0, k, 4] : Fin 3 → Fin 5) FrameLoad.machine
def parse3 := Composition.machine (fl 1) (Composition.machine (fl 2) (fl 3))
def parseM := Rewind.machine parse3
def parseCost (c : Nat) : Nat := 7 + 1 + ((4 * c + 3) + 1 + (4 * c + 3))

/-! ## Binary → unary, docked (dirty scratch) -/

def unaryM {U : Nat} (sl : Fin 7 → Fin U) := RecoveryFocus.machine sl RepairSource.RecoveryProjectionDimension.machine

/-! ## One factor -/

def accM :=
  Composition.machine (RecoveryFocus.machine (![0, 8, 9, 10, 11, 7] : Fin 6 → Fin 30) parseM)
  (Composition.machine (unaryM (![8, 12, 13, 14, 15, 16, 17] : Fin 7 → Fin 30))
  (Composition.machine (Count.sumM (3 : Fin 30) 16 6 7)
  (Composition.machine (unaryM (![9, 18, 19, 20, 21, 22, 23] : Fin 7 → Fin 30))
  (Composition.machine (Count.mulM (1 : Fin 30) 20 4 7)
  (Composition.machine (unaryM (![10, 24, 25, 26, 27, 28, 29] : Fin 7 → Fin 30))
  (Count.mulM (2 : Fin 30) 26 5 7))))))

def ub (bits : List Bool) : Nat := RepairSource.RecoveryProjectionDimension.budget bits

def accCost (s : Bool) (n d c Na Da sa : Nat) : Nat :=
  (2 * parseCost c + 2) + 1 + (ub [s] + 1 + ((2 * (sa + s.toNat) + 6) + 1 + (ub (binary c n) + 1 +
    ((2 * (Na * (2 * n + 3) + 2) + 2) + 1 + (ub (binary c d) + 1 + (2 * (Da * (2 * d + 3) + 2) + 2))))))

end
end NearCubicWires.SourceFactorSel.CoefAcc

