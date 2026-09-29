import Proof.Amplification.RecoveryWitnessPolicy
import Proof.Circuits.CanonicalInputLiftedBooleanCircuitEncoding
import Proof.Circuits.DecompositionInputBudget
import Proof.Circuits.DecompositionStreamReset

/-! Literal source request after native compact substitution. Input-axis
lifting handles the source's minimum arity; isolated nodes handle its size
condition. These semantic/code identities do not claim a paid producer. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestBoundary
open RepairRepresentation SourceInterfaces ExecutableInterfaces CanonicalBinary
open InputLiftedBooleanCircuit CanonicalInputLiftedBooleanCircuitEncoding
open ProjectionPCPPadding RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def domain (a : PointwisePCPPAlgorithm) (n : ℕ) := max n a.minimumArity
def lifted (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :=
  liftBooleanCircuitInputs c (Nat.le_max_left n a.minimumArity)
def request (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) : PCPPRequest a.minimumArity :=
  pointwiseRequest a (lifted a c) (Nat.le_max_right n a.minimumArity)
def padding (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) := domain a n-c.size

theorem request_size (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    (request a c).circuit.size=max c.size (domain a n) := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity,BooleanCircuit.padSize_size,
    lifted,liftBooleanCircuitInputs_size]
  unfold domain
  omega

theorem request_eval (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n)
    (x : BitInput (domain a n)) :
    (request a c).circuit.eval x=c.eval (prefixBits (Nat.le_max_left n a.minimumArity) x) := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity_eval,lifted,liftBooleanCircuitInputs_eval]

end NearCubicWires.RepairOrdinary.PCPPRequestBoundary
