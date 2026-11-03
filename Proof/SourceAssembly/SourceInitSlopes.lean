import Proof.SourceAssembly.SourceRestLayout
import Proof.MachineModel.OrdinaryMatrixBucketDivide

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.InitSlopes
noncomputable section

/-! ## 1. Two extra padded stages -/

/-! ## 2. The local layout (57 tapes) -/

def sa : Fin 3 → Fin 57 := ![0, 2, 3]
def sb : Fin 27 → Fin 57 := fun j => ⟨if j.val = 0 then 2 else 3 + j.val, by
  have := j.isLt; split_ifs <;> omega⟩
def sc : Fin 3 → Fin 57 := ![28, 30, 31]
def sd : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 57 := fun j => ⟨if j.val = 0 then 30 else 31 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
  split_ifs <;> omega⟩
def se : Fin 3 → Fin 57 := ![36, 47, 48]
def sf : Fin 3 → Fin 57 := ![0, 49, 50]
def sg : Fin 4 → Fin 57 := ![49, 47, 51, 52]
def sh : Fin 3 → Fin 57 := ![1, 53, 54]
def si : Fin 4 → Fin 57 := ![51, 53, 55, 56]


/-- The divisor `200(K+2)`. -/
abbrev dv (L q : ℕ) : ℕ := 200*(normalizedLiveCount q L+1+1)

def machine (L : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine sa (UWalkUnary.machine true false))
    (RecoveryFocus.machine sb (PCJ6e421fabe2aa4155_SourceLiveCount.machine L)))
    (RecoveryFocus.machine sc (UWalkUnary.machine false true)))
    (RecoveryFocus.machine sd (PCPSerializerCapacity.Power.machine 1 200)))
    (RecoveryFocus.machine se (DimensionTemplate.machine false)))
    (RecoveryFocus.machine sf (UWalkUnary.machine false false)))
    (RecoveryFocus.machine sg MatrixBucketDivide.machine))
    (RecoveryFocus.machine sh (DimensionTemplate.machine false)))
    (RecoveryFocus.machine si ClockUnaryProduct.machine)

def cost (L q Ms : ℕ) : ℕ :=
  let K := normalizedLiveCount q L
  ((((((((2*q+6)+1+PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)+1+(2*K+6))+1+
    PCPSerializerCapacity.Power.budget 1 200 (K+1))+1+(2*dv L q+8))+1+(2*q+6))+1+(8*q+6))+1+
    (2*Ms+8))+1+(2*(q/dv L q*(2*Ms+3)+2)+2)

/-! ## 3. The run -/

end
end NearCubicWires.SourceConstruction.InitSlopes
end
