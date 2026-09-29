import Proof.Wire_3_5.Primitive.Writers.GeoFront
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface

/-! # C4 per-call setup (item 3), part 1: the docked front machines, generic in the slot map

P3:3119-3120 ("The algorithm receives polynomial-bit integer circuit descriptions") and P3:2939-2941 (the seed's
field and its arithmetic "can be found and implemented in `2^{O(ℓ)}` elementary preprocessing time"): the C4 stages'
per-call setup reads its numbers from the request word, in unary registers whose capacity it first writes in unary.
Each front machine is docked into the stage's bank by an injective slot map; the bank off the slots is unchanged:

* **`unframe_dock`** (C2's `Unframe`: the raw request `w` from `frame w`);
* **`capR_dock`** (base `CapReader`: `1^v` twice from the self-delimiting binary `natWord v ++ sfx`);
* **`ucalc_dock`** (base `UnaryCalc`: `1^{C(n+1)^D}` from `1^n`, the input kept);
* **`wr_dock`** (a writer's run `WriterIfaceJ.WriterRun`), **`c3_dock`** (the C3 request writer's `C3Run`).

Paper quantities of the main types: the request word, its numbers in unary, the writers' words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## The raw request -/

/-- The unframing machine (C2's `Unframe` under the masked reset: every head back at `0`). -/
noncomputable def unM := MaskedReset.machine Unframe.machine (fun _ => true)

/-! ## `1^v` from the binary `natWord v` -/

/-- The capacity reader (base `CapReader` under the masked reset). -/
noncomputable def crM := MaskedReset.machine PCJ45bee56da9f34d5a_CapReader.machine (fun _ => true)

/-- The capacity reader's step bound. -/
def crCost (v : ℕ) : ℕ := 2 * (8 * v + 20 * natBitLength v + 17) + 2

/-! ## `1^{C(n+1)^D}` from `1^n` -/

/-! ## Writers -/

/-- A clock-join ready run is a `Step` with every head at `0` at both ends. -/
theorem cjStep {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

end NearCubicWires.WireExponent3_5.PrimT.C4Set
