import Proof.Packets.SubstitutionOuterScan
import Proof.Packets.SubstitutionOuterAccumulate
import Proof.Packets.SubstitutionOuterReload

/-! One complete executed monomial step of the frozen substitution: consume
all code bits in reverse, accumulate the product on the left, restore one,
and physically reload the code counter for the next monomial. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def body := Composition.machine scanMachine (Composition.machine accumulate reload)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
