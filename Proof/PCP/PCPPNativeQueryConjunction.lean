import Proof.PCP.PCPPNativeMetadata

/-! The physically computed resources and original normalized Q-loop feed
the actual conjunction seed. The next clause base and accumulator are read
from execution, and the constant-true node has already been appended. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryConjunction
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seedSlots : Fin 5 → Fin 278 := ![99,275,276,277,102]
theorem seed_injective : Function.Injective seedSlots := by decide
noncomputable def first := TapeEmbedding.machine 3 PCPPNativeResourceQuery.machine
noncomputable def second := RecoveryFocus.machine seedSlots PCPPNativeConjunctionStart.machine
noncomputable def machine := Composition.machine first second
def input (bits fields : List Bool) (R Q s M Lq Lc : ℕ) : Fin 278 → List Bool :=
  Fin.addCases (m := 275) (n := 3) (motive := fun _ => List Bool)
    (PCPPNativeResourceQuery.input bits fields R Q s M Lq Lc) (fun _ => [])
def budget (R Q s M Lq Lc : ℕ) := PCPPNativeResourceQuery.budget R Q s M Lq Lc+1+
  PCPPNativeConjunctionStart.budget (Q*(2*s+1))
noncomputable def queryBytes (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width ≤ R) (hQ : p.queries ≤ Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :=
  (PCPPNative.queryNodesPrefix 0 oracle ((p.normalized R Q hR hQ).queryAddressBits x) Q).flatMap PCPPRequestNodeSchema.native

end NearCubicWires.RepairOrdinary.PCPPNativeQueryConjunction
