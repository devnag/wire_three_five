import Proof.CaseAnalysis.RowsUniversalAtoms

/-! A.2 lowering uses one fixed polynomial on the pooled child cache for every
input. The two cache entries cost one additional child-count bit, without
changing the monomial degree. -/
namespace NearCubicWires.RepairSource.CloseoutRowsUniversal
open SupplierPipeline RepairRepresentation CanonicalFourfoldRowProgram CloseoutRawRows
open RepairOrdinary ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {q : ℕ}

def atomOfCode (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (code : ℕ) : StructuralGF2Polynomial :=
  if h : code<occ.length then residualAtom a live occ ⟨code,h⟩ else structuralGF2Zero

def lower (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (P : StructuralGF2Polynomial) :=
  structuralGF2Substitute (atomOfCode a live occ) P

theorem atom_degree (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (code : ℕ) :
    RawMonomialDegreeAtMost 1 (atomOfCode a live occ code):=by
  unfold atomOfCode
  split
  · exact residual_degree a live occ _
  · exact rawDegree_zero _

theorem lower_degree (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (P : StructuralGF2Polynomial)
    (d : ℕ) (hP : RawMonomialDegreeAtMost d P) :
    RawMonomialDegreeAtMost d (lower a live occ P):=
  rawDegree_substitute _ (atom_degree a live occ) P hP

end
end NearCubicWires.RepairSource.CloseoutRowsUniversal
