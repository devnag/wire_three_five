import Proof.CaseAnalysis.FinalSupplierRowInput

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.ThresholdCompiler
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierTable

noncomputable section

section Table
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)
  (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
  (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s)

/-- **The printed signed score table**, mod `2^Q`: entry `(i,j)` is the number of bank
polynomials that evaluate to `1` at the half-cube point `(i,j)` (`rowValues`). -/
def table :
    Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U →
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U → ℕ :=
  fun i j => CompetitorCountTable.rowValues
    (CloseoutRowsCacheInput.family (pool a live occ s harity) (bank a live occ s harity P))
    (rowInput a live occ s harity P w hs hmon hpos hload) i j

end Table

section C10

end C10


end

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierTable
