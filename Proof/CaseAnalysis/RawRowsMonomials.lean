import Proof.CaseAnalysis.RawRowsModes

/-! Raw monomial degrees through the actual masked and powered-walk rows.
Every literal substitution has degree at most one; no cancellation is used. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierToeplitz SupplierToeplitzCore
open SupplierWalk SupplierRadix SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem rawDegree_mono {a b : ℕ} {P : StructuralGF2Polynomial}
    (h : RawMonomialDegreeAtMost a P) (hab : a ≤ b) : RawMonomialDegreeAtMost b P :=
  fun m hm => (h m hm).trans hab

theorem rawDegree_add {d : ℕ} {P Q : StructuralGF2Polynomial}
    (hP : RawMonomialDegreeAtMost d P) (hQ : RawMonomialDegreeAtMost d Q) :
    RawMonomialDegreeAtMost d (structuralGF2Add P Q) := by
  intro m hm
  exact (List.mem_append.mp hm).elim (hP m) (hQ m)

theorem rawDegree_one (d : ℕ) : RawMonomialDegreeAtMost d structuralGF2One := by
  intro m hm
  simp only [structuralGF2One,List.mem_singleton] at hm
  subst m
  simp

theorem rawDegree_product (a : ℕ) (ps : List StructuralGF2Polynomial)
    (hp : ∀ P ∈ ps, RawMonomialDegreeAtMost a P) :
    RawMonomialDegreeAtMost (a*ps.length) (structuralGF2Product ps) := by
  induction ps with
  | nil => exact rawDegree_one _
  | cons P ps ih =>
    have h := rawDegree_mul (hp P (by simp)) (ih (fun Q hQ => hp Q (by simp [hQ])))
    simpa only [structuralGF2Product,List.foldr_cons,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_comm] using h

theorem rawDegree_substitute {d : ℕ} (atom : ℕ → StructuralGF2Polynomial)
    (ha : ∀ code, RawMonomialDegreeAtMost 1 (atom code)) (P : StructuralGF2Polynomial)
    (hP : RawMonomialDegreeAtMost d P) :
    RawMonomialDegreeAtMost d (structuralGF2Substitute atom P) := by
  induction P with
  | nil => exact rawDegree_zero _
  | cons m P ih =>
    apply rawDegree_add
    · have hm := rawDegree_product 1 (m.map atom) (by
        intro Q hQ
        obtain ⟨code,_,rfl⟩ := List.mem_map.mp hQ
        exact ha code)
      simp only [List.length_map,Nat.one_mul] at hm
      exact rawDegree_mono hm (hP m (by simp))
    · exact ih (fun n hn => hP n (by simp [hn]))

def coordinateDegree {q : ℕ} (gs : List (SupportedNormalizedGate q)) (L den : ℕ) : ℕ :=
  let active := touchingCost (occurrenceSupport gs) (normalizedLiveSet gs L)
  canonicalWalkLength den * structuralListCoordinateRawDegree (canonicalGradedDepth active)
    (executableGradedWindow active) gradedTerminalWindow

end
end NearCubicWires.RepairSource.CloseoutRawRows
