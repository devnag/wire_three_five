import Proof.Rows.NativeScaleInput

/-! One native signed coefficient is read, reduced, multiplied by the resident
scale, and appended to the modular summand stream. Both consumers return the
same next bank; only the native source and append cursors advance. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey PCJ45bee56da9f34d5a_NativeScaleInput
noncomputable section


def budget (negate : Bool) (z : Int) (w F U : Nat):=
  2*C10NativeResidueCallback.coreBudget negate z w+2*F+1024*(w+1)^2+10*U+18*w+55

end
end PCJ45bee56da9f34d5a_NativeScaleRun
