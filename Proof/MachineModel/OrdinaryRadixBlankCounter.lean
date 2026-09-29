import Proof.MachineModel.OrdinaryRadixSemantics
import Proof.MachineModel.OrdinaryZeroUnpadding

/-! The actual sorter with a fresh empty counter tape. Counter cells are
allocated by the existing executed writes, so no initialization pass is needed.
The record stream and unary width still come from the actual caller. -/
namespace NearCubicWires.RepairOrdinary.RadixBlankCounter
open LocalBitMultitape StablePartition RadixWorkspace RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (capacity : ℕ) : Fin 5 → ℕ := fun i => if i.val = 3 then 2 * capacity else 0

def tapes {capacity : ℕ} {rs : List Record} (w : State capacity rs) (width : ℕ) :
    Fin 5 → List Bool := fun i => if i.val = 3 then [] else
      (RadixIteration.boundary w false 0 width).tapes i

theorem padded_initial {capacity : ℕ} {rs : List Record} (w : State capacity rs) (width : ℕ) :
    ZeroPadding.config (capacities capacity) (initialConfiguration RadixIteration.machine (tapes w width)) =
      initialConfiguration RadixIteration.machine (RadixIteration.boundary w false 0 width).tapes := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;>
      simp [ZeroPadding.config, capacities, tapes, initialConfiguration,
        RadixIteration.boundary, UnaryController.boundary, State.phaseTapes, State.tapes,
        layout, Fin.addCases, ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.RadixBlankCounter
