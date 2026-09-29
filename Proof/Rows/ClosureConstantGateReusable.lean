import Proof.Rows.ClosureConstantGate
import Proof.Rows.ClosureReusable48

/-! Complete reusable X/C frozen-gate field computation with a uniform
quadratic bound derived from the original retained description. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateReusable
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline
open VerifierDecoding SignedSortKey
open scoped BigOperators

variable {q : Nat} (live : Finset (Fin q)) (g : NormalizedThresholdGate q)
def C (w : Nat) := 8*w+12
def E (B q : Nat) := B+15*q+3


end NearCubicWires.P1Closure.ConstantGateReusable
