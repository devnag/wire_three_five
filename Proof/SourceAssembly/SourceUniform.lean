import Proof.SourceAssembly.SourceOnce
import Proof.Circuits.DecompositionCountPosition

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
namespace NearCubicWires.SourceConstruction.Uniform
noncomputable section

/-! ## 1. The stages, padded -/

/-! ## 2. The local layout -/

def psV (j : ℕ) : ℕ := if j = 0 then 0 else 10 + j
def prV (j : ℕ) : ℕ := if j = 0 then 0 else 25 + j
def psS : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 43 := fun j => ⟨psV j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  unfold psV; split_ifs <;> omega⟩
def psR : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 43 := fun j => ⟨prV j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  unfold prV; split_ifs <;> omega⟩

def t0 : Fin 3 → Fin 43 := ![15, 3, 7]
def t1 : Fin 3 → Fin 43 := ![30, 4, 8]
def t2 : Fin 3 → Fin 43 := ![0, 5, 9]
def t3 : Fin 3 → Fin 43 := ![2, 6, 10]

/-- The erase mask: `1^V` and its log. -/
def mask : Fin 43 → Bool := fun i => i.val = 0 || i.val = 1
/-- The head moves: the four drivers one cell right. -/
def dirs : Fin 43 → HeadMove := fun i => if 3 ≤ i.val ∧ i.val ≤ 6 then HeadMove.right else HeadMove.stay

def machine (cS cR : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine psS (PCPSerializerCapacity.Power.machine 1 cS))
    (RecoveryFocus.machine t0 (DimensionTemplate.machine false)))
    (RecoveryFocus.machine psR (PCPSerializerCapacity.Power.machine 1 cR)))
    (RecoveryFocus.machine t1 (DimensionTemplate.machine false)))
    (RecoveryFocus.machine t2 (DimensionTemplate.machine true)))
    (RecoveryFocus.machine t3 (DimensionTemplate.machine false)))
    (CloseoutWitness.SelectedErase.machine mask (41 : Fin 43) (42 : Fin 43)))
    (DecompositionCountPosition.move dirs)

def cost (cS cR V b Rc : ℕ) : ℕ :=
  ((((((PCPSerializerCapacity.Power.budget 1 cS V+1+(2*(cS*(V+1))+8))+1+
    PCPSerializerCapacity.Power.budget 1 cR V)+1+(2*(cR*(V+1))+8))+1+(2*V+8))+1+(2*b+8))+1+
    (2*Rc+4))+1+1

/-! ## 3. The run -/


end
end NearCubicWires.SourceConstruction.Uniform
end
