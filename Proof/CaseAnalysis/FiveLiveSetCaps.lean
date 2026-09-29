import Proof.CaseAnalysis.RawRowsPaperCaps

/-! Live-set-generic ports of the paper cap and shape lemmas (plan §12.1,
steps 1-2). The only property of the legacy `normalizedLiveSet` those lemmas
used is the touching inequality `q*active ≤ K*mass`; the accepted cyclic
selector supplies exactly that as `Geometry.touch`, so every statement below
takes an arbitrary live set `I` and that inequality as a hypothesis. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierCapacity
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairOrdinary.CloseoutRowsRawLogShape
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- Depth and window sum at an arbitrary live set; with `I := CyclicChoice.live occ L`
these are the quantities inside the accepted `Packets.coordinateDegree`. -/
def rowDepthAt {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) : ℕ :=
  canonicalGradedDepth (touchingCost (occurrenceSupport gs) I)
def windowSumAt {q : ℕ} (gs : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) : ℕ :=
  ∑ i : Fin (rowDepthAt gs I), executableGradedWindow (touchingCost (occurrenceSupport gs) I) i

end
end NearCubicWires.RepairSource.CloseoutRawRows
