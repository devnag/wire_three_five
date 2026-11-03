import Proof.Rows.FullGateBounds

/-! Consume the existing paid reusable gate on an arbitrary full assignment.
False backing is added only to retained source/mask masters after the run proof,
so it does not enlarge the logical evaluator capacity or create a size cycle. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FullGateRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine

def masterCaps (H : Nat) (i : Fin 108) := if i=0 ∨ i=1 then H else 0

theorem pad_cold (source mask : List Bool) (q w C R H U : Nat) (out : List Bool) :
    (fun i=>ZeroPadding.pad (masterCaps H i) (cold (words source mask q w C R) U out i)) =
      cold (words (ZeroPadding.pad H source) (ZeroPadding.pad H mask) q w C R) U out := by
  funext i;fin_cases i <;>first |rfl |exact ZeroPadding.pad_zero _


end
end PCJ45bee56da9f34d5a_FullGateRun
