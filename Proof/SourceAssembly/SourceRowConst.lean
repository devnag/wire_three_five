import Proof.SourceAssembly.SourceRewindOnce
import Proof.PCP.PCPUnarySplit

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.RowConst
noncomputable section

/-! ## 1. Padded stages -/


/-! ## 2. Bookkeeping, generic in the universe -/

/-! ## 3. The local layout (79 tapes) -/

def sA : Fin 3 → Fin 79 := ![0, 1, 2]
def sB : Fin 27 → Fin 79 := fun j => ⟨if j.val = 0 then 1 else 2 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def sC : Fin 4 → Fin 79 := ![0, 27, 29, 30]
def sD : Fin 3 → Fin 79 := ![29, 31, 32]
def sE : Fin 4 → Fin 79 := ![31, 33, 34, 35]
def sF : Fin 4 → Fin 79 := ![33, 36, 37, 38]
def sG : Fin 4 → Fin 79 := ![33, 37, 39, 40]
def sH : Fin 3 → Fin 79 := ![27, 41, 42]
def sI : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 79 := fun j => ⟨if j.val = 0 then 41 else 42 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  split_ifs <;> omega⟩
def sJ : Fin 3 → Fin 79 := ![41, 58, 59]
def sK : Fin 3 → Fin 79 := ![58, 60, 61]
def sL : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 79 := fun j => ⟨if j.val = 0 then 60 else 61 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  split_ifs <;> omega⟩
def sM : Fin 4 → Fin 79 := ![66, 39, 77, 78]


def machine (L cM : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine sA (UWalkUnary.machine true false))
    (RecoveryFocus.machine sB (PCJ6e421fabe2aa4155_SourceLiveCount.machine L)))
    (RecoveryFocus.machine sC MatrixUnaryDifference.resetMachine))
    (RecoveryFocus.machine sD (UWalkUnary.machine false false)))
    (RecoveryFocus.machine sE PCPUnarySplit.machine))
    (RecoveryFocus.machine sF ClockUnarySum.machine))
    (RecoveryFocus.machine sG ClockUnarySum.machine))
    (RecoveryFocus.machine sH (UWalkUnary.machine false false)))
    (RecoveryFocus.machine sI (PCPSerializerCapacity.Power.machine 1 cM)))
    (RecoveryFocus.machine sJ (DimensionTemplate.machine true)))
    (RecoveryFocus.machine sK (UWalkUnary.machine false true)))
    (RecoveryFocus.machine sL (PCPSerializerCapacity.Power.machine 1 3)))
    (RecoveryFocus.machine sM ClockUnarySum.machine)

def cost (L cM q : ℕ) : ℕ :=
  let K := normalizedLiveCount q L
  let s := q - K
  let c := (s+1)/2
  ((((((((((((2*q+6)+1+PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)+1+(2*q+8))+1+(2*s+6))+1+
    (2*s+4))+1+(2*c+6))+1+(2*(c+c)+6))+1+(2*K+6))+1+PCPSerializerCapacity.Power.budget 1 cM K)+1+
    (2*K+8))+1+(2*(K+1)+6))+1+PCPSerializerCapacity.Power.budget 1 3 (K+2))+1+
    (2*(3*(K+2+1)+(c+c))+6)

/-! ## 4. The run -/

end
end NearCubicWires.SourceConstruction.RowConst
end
