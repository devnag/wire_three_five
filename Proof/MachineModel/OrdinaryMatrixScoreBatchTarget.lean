import Proof.MachineModel.OrdinaryMatrixScoreBatchCodec

/-! Local implementation targets, not source assumptions. No inhabitant of
these targets is supplied here. Every reusable invocation admits arbitrary
bounded old workspace and must return bounded workspace with local heads0;
empty workspace is the cold specialization. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBatch
open LocalBitMultitape SupplierPrinter SignedSortKey RepairRepresentation SourceInterfaces
open WilliamsProductCertificate
open WilliamsLoaderForms (encodedNatCellTape rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def gateWord (r : Request) (gate : Fin r.Gates) : List Bool :=
  natWord r.d++natWord r.p++cutWord r.p (r.cuts.get gate)
def gateRecords (r : Request) (gate : Fin r.Gates) : List Bool :=
  StablePartition.stream (DominanceSort.records r.S r.M (leftScore r) (rightScore r) gate)

def signedLeft (r : Request) := padSignedInner (Capacity := r.Capacity)
  (reindexedLaterBucketLeft (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize) (weight r))
def booleanRight (r : Request) := padBooleanInner (Capacity := r.Capacity)
  (reindexedLaterBucketRight (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize))
def planeCounts (r : Request) (negative : Bool) (bit : ℕ) : List Bool :=
  encodedNatCellTape (natBitLength r.U) (rowMajorNatMatrix (integerMatrixProduct
    (fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit) (booleanRight r)))
def factor (bit : ℕ) : List Bool := frame (List.replicate bit false++[true])

/-- Each packet has one sign bit, one framed factor, then exactly U² raw
native-width counts. Zero counts are present, in unchanged row-major order. -/
def packet (r : Request) (negative : Bool) (bit : ℕ) : List Bool :=
  [negative]++factor bit++planeCounts r negative bit
def output (r : Request) : List Bool := (List.range r.p).flatMap
  (fun bit => packet r false bit++packet r true bit)

theorem planeCounts_length (r : Request) (negative : Bool) (bit : ℕ) :
    (planeCounts r negative bit).length=r.U^2*natBitLength r.U := by
  simp [planeCounts,encodedNatCellTape,WilliamsLoaderForms.fixedWidthNatBits,
    List.length_flatMap,rowMajorNatMatrix_length,pow_two]

end NearCubicWires.RepairOrdinary.MatrixScoreBatch
