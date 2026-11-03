import Proof.Rows.PhysicalFocusBoundary

/-! Preserve a fixed prefix of resident tapes around an actual execution. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalPrepend
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def machine {t states : Nat} (e : Nat) (program : Machine t states) :=
  RecoveryFocus.machine (fun i : Fin t=>i.natAdd e) program

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalPrepend
