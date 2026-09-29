import Proof.Supplier.SupplierEstimator

/-! Actual finite offset families of the A.13 symmetric and threshold rows.
These bounds justify a polynomial number of table scans at a bounded-wire
fourfold caller. They do not assume a runtime offset tape has been produced. -/
namespace NearCubicWires.RepairOrdinary.RowOffsets
open SupplierPipeline SupplierEstimator SupplierPrime
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev SymmetricOffsets (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :=
  (i : Fin r.circuits.length) → Fin ((r.circuits.get i).bottomCount+1)

/-- These are exactly the residual constants read by canonicalSymmetricCircuitRow. -/
def symmetricOffsets (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput r.q) : SymmetricOffsets r :=
  fun i => ⟨occurrenceResidualConstantCount (symmetricFourfoldOccurrences r)
    liveScale input (symmetricCircuitMask r i), by
    have h := symmetricCircuitResidualCount_reconstruction r liveScale input i
    have hb := ((r.circuits.get i).acceptedBottomCount input).isLt
    omega⟩

end NearCubicWires.RepairOrdinary.RowOffsets
