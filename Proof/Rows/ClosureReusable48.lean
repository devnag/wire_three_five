import Proof.Assembly.RowProduction

/-! Reuse the checked 48-tape restoration layout for the second physical
source worker, the X/C constant gate. All runtime templates remain inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.Reusable48
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open HardwireReusable hiding machine child input padded masters budget run

noncomputable def child {s : Nat} (p : Machine 48 s) :=
  RecoveryFocus.machine maskSlots (MaskedReset.machine p selected)
noncomputable def machine {s : Nat} (p : Machine 48 s) :=
  Composition.machine (Composition.machine (Composition.machine (child p) (move false)) restore) (move true)

end NearCubicWires.P1Closure.Reusable48
