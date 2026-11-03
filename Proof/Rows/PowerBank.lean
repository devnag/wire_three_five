import Proof.Rows.ScalarReplace

/-! The coefficient mapper's actual bank with a retained full-width base and
one isolated product destination. The growing coefficient output stays at64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_ResidueScaleCell.palette

def factorCap (U : Nat) (i : Fin 91) := if i=28 then U else 0
def base (a p w F U : Nat) (source out coefficient : List Bool) (i : Fin 91) :=
  ZeroPadding.pad (factorCap U i) (PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U source out coefficient i)
def bank (a B p w F U q : Nat) (source out coefficient temp : List Bool) : Fin 94→List Bool :=
  Fin.addCases (m:=91) (n:=3) (motive:=fun _=>List Bool) (base a p w F U source out coefficient)
    ![CompareMachine.word q,ZeroPadding.pad U (frame (binary w B)),ZeroPadding.pad U temp]


end
end PCJ45bee56da9f34d5a_PowerBank
