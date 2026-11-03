import Proof.SourceAssembly.SourceUniform

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator PCJ9eff70d512234a4c_Fixed
namespace NearCubicWires.SourceConstruction.RowWidth
noncomputable section

/-! ## 1. The value `rowWidth` is forced to -/

/-- The calculator's value. -/
def rw (M2 U0 L : ℕ) : ℕ := M2 * (L+1) + U0

/-! ## 2. Padded stages -/

/-! ## 3. The calculator -/

def sa : Fin 3 → Fin 16 := ![0, 6, 7]
def sb : Fin 4 → Fin 16 := ![1, 6, 8, 9]
def sc : Fin 4 → Fin 16 := ![8, 2, 10, 11]
def sd : Fin 3 → Fin 16 := ![10, 4, 12]
def sf : Fin 4 → Fin 16 := ![10, 3, 13, 14]
def sg : Fin 3 → Fin 16 := ![13, 5, 15]
def dirIn : Fin 16 → HeadMove := fun i => if i.val = 3 then HeadMove.left else HeadMove.stay
def dirOut : Fin 16 → HeadMove := fun i => if 3 ≤ i.val ∧ i.val ≤ 5 then HeadMove.right else HeadMove.stay


def machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine sa (DimensionTemplate.machine true))
    (RecoveryFocus.machine sb ClockUnaryProduct.machine))
    (RecoveryFocus.machine sc ClockUnarySum.machine))
    (RecoveryFocus.machine sd (DimensionTemplate.machine false)))
    (DecompositionCountPosition.move dirIn))
    (RecoveryFocus.machine sf ClockUnaryProduct.machine))
    (RecoveryFocus.machine sg (DimensionTemplate.machine false)))
    (DecompositionCountPosition.move dirOut)

def cost (L M2 U0 N : ℕ) : ℕ :=
  let ca := 2*L+8
  let cb := 2*(M2*(2*(L+1)+3)+2)+2
  let cc := 2*(M2*(L+1)+U0)+6
  let cd := 2*rw M2 U0 L+8
  let cf := 2*(rw M2 U0 L*(2*N+3)+2)+2
  let cg := 2*(rw M2 U0 L*N)+8
  ((((((ca+1+cb)+1+cc)+1+cd)+1+1)+1+cf)+1+cg)+1+1


end
end NearCubicWires.SourceConstruction.RowWidth
end
