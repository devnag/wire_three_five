import Proof.SourceAssembly.SourceInitSlopes
import Proof.SourceAssembly.SourcePrologue
import Proof.CaseAnalysis.FinalAppendWorkspaceInit

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
namespace NearCubicWires.SourceConstruction.InitEnc
noncomputable section

/-! ## 1. Three extra padded stages -/

/-! ## 2. The local layout (119 tapes) -/

/-- A `poly_step 1 c` dock with its input on tape 0 and its private tapes from `base+1`. -/
def sp (base : ℕ) (h : base + 16 ≤ 119) : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 119 :=
  fun j => ⟨if j.val = 0 then 0 else base + j.val, by
    have := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
    split_ifs <;> omega⟩

def s1 := sp 0 (by decide)
def s2 : Fin 5 → Fin 119 := ![5, 16, 17, 18, 19]
def s3 := sp 19 (by decide)
def s4 : Fin 4 → Fin 119 := ![24, 35, 36, 37]
def s5 : Fin 4 → Fin 119 := ![24, 38, 39, 40]
def s6 : Fin 3 → Fin 119 := ![24, 41, 42]
def s7 : Fin 3 → Fin 119 := ![41, 43, 44]
def s8 := sp 44 (by decide)
def s9 : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 119 := fun j => ⟨60 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
  omega⟩
def s10 : Fin 4 → Fin 119 := ![49, 65, 76, 77]
def s11 : Fin 42 → Fin 119 := fun j => ⟨if j.val = 0 then 0 else 77 + j.val, by
  have := j.isLt; split_ifs <;> omega⟩


def machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine
    (RecoveryFocus.machine s1 (PCPSerializerCapacity.Power.machine 1 2))
    (RecoveryFocus.machine s2 ClockNormalize.machine))
    (RecoveryFocus.machine s3 (PCPSerializerCapacity.Power.machine 1 21)))
    (RecoveryFocus.machine s4 ClockUnarySum.machine))
    (RecoveryFocus.machine s5 ClockUnarySum.machine))
    (RecoveryFocus.machine s6 (DimensionTemplate.machine false)))
    (RecoveryFocus.machine s7 (UWalkUnary.machine false true)))
    (RecoveryFocus.machine s8 (PCPSerializerCapacity.Power.machine 1 40)))
    (RecoveryFocus.machine s9 (PCPSerializerCapacity.Power.machine 1 14)))
    (RecoveryFocus.machine s10 ClockUnarySum.machine))
    (RecoveryFocus.machine s11 CloseoutFinalC10AppendWorkspaceInit.machine)

/-- `r = 21(b+1)`. -/
abbrev rr (b : ℕ) : ℕ := 21*(b+1)

def cost (b : ℕ) : ℕ :=
  (((((((((PCPSerializerCapacity.Power.budget 1 2 b+1+(4*(2*(b+1))+4))+1+
    PCPSerializerCapacity.Power.budget 1 21 b)+1+(2*rr b+6))+1+(2*rr b+6))+1+(2*rr b+8))+1+
    (2*rr b+6))+1+PCPSerializerCapacity.Power.budget 1 40 b)+1+PCPSerializerCapacity.Power.budget 1 14 0)+1+
    (2*(40*(b+1)+14*(0+1))+6))+1+CloseoutFinalC10AppendWorkspaceInit.budget b

/-! ## 3. The run -/

end
end NearCubicWires.SourceConstruction.InitEnc
end
