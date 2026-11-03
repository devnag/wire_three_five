import Proof.Packets.PacketsXNormalizerOperations

/-! Exact ordered transport between finite physical coordinates and the
original natural literal codes. Fin.val preserves ordering and all codes;
this is stronger than evaluation or permutation equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedFiniteTransport
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
variable {C : Nat}


def maskNat (C : Nat) (m : List Nat) : List Bool := List.ofFn (fun i : Fin C=>decide (i.val∈m))


end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedFiniteTransport
