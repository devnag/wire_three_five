import Proof.MachineModel.ClosureBinaryPreparedPayload

/-! Minimal semantic row descriptors and the actual uniform output width.
This defines no encoded source, producer, enumeration, mask or reusable bank.
Those remain the whole transaction's physical obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownFamilyAudit
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutFinal CanonicalFourfoldRowProgram ThresholdCompiler
open CompetitorSelectedCount P1Closure

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (w degree : Nat)

/-- Only mathematical row data. None of these fields supplies physical words. -/
structure Descriptor where
  polynomial : StructuralGF2Polynomial
  monomials_fit : (CloseoutRowsUniversal.lower a live occ polynomial).length<2^w
  degree_fit : CloseoutRawRows.RawMonomialDegreeAtMost degree polynomial
  select : Fin (2^((s+1)/2)) → Fin (2^((s+1)/2)) → Bool

attribute [local irreducible] BinaryPool.pool CompactBounds.radix

end NearCubicWires.P1TopDownFamilyAudit
