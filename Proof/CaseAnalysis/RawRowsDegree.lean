import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.Circuits.ValidatorPolynomialDomination

/-! The paper's existing raw list recurrence, applied to the current GF2
constructors. Reuses the mathematical recurrence from ParityCapFirstProofs
without its obsolete executor imports or mode-specific wrappers. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierListPolynomial SupplierListSchedule
open SupplierToeplitz SupplierToeplitzCore SupplierWalkBridge
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def RawMonomialDegreeAtMost
    (degree : ℕ) (polynomial : StructuralGF2Polynomial) : Prop :=
  ∀ monomial ∈ polynomial, monomial.length ≤ degree

theorem rawDegree_zero (degree : ℕ) :
    RawMonomialDegreeAtMost degree structuralGF2Zero := by
  intro monomial hmonomial
  simp [structuralGF2Zero] at hmonomial

theorem rawDegree_mul
    {leftDegree rightDegree : ℕ}
    {left right : StructuralGF2Polynomial}
    (hleft : RawMonomialDegreeAtMost leftDegree left)
    (hright : RawMonomialDegreeAtMost rightDegree right) :
    RawMonomialDegreeAtMost (leftDegree + rightDegree)
      (structuralGF2Mul left right) := by
  intro monomial hmonomial
  unfold structuralGF2Mul at hmonomial
  obtain ⟨leftMonomial, hleftMonomial, hrightMap⟩ :=
    List.mem_flatMap.mp hmonomial
  obtain ⟨rightMonomial, hrightMonomial, rfl⟩ :=
    List.mem_map.mp hrightMap
  rw [List.length_append]
  exact Nat.add_le_add
    (hleft leftMonomial hleftMonomial)
    (hright rightMonomial hrightMonomial)

def structuralListCoordinateRawDegreeFrom
    (depth : ℕ) (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) : ℕ :=
  if hlevel : level < depth then
    structuralListCoordinateRawDegreeFrom depth window terminalWindow
        (level + 1) +
      2 * window ⟨level, hlevel⟩
  else
    terminalWindow
termination_by depth - level
decreasing_by omega

def structuralListCoordinateRawDegree
    (depth : ℕ) (window : Fin depth → ℕ) (terminalWindow : ℕ) : ℕ :=
  structuralListCoordinateRawDegreeFrom depth window terminalWindow 0


end
end NearCubicWires.RepairSource.CloseoutRawRows
