import Proof.Wire_3_5.FinalPass.SeamsS4

/-! # S4's seam at the machine level: the seeds phase as one machine on S4's word layout

`SeedsWM` asks for S4 as ONE word program. It cannot be one: the seed's filter table
`tableWord (filterTable P e L)` (P3:2036-2101) is written only by C5's stage-6 builder `Filt.builderM`, a machine
(`Filt.stage6_step : Step builderM …`), fed by the walk bank's machine (PA's `FiltPipe.filtPipeM` composes them with
`Step.seq`). So S4 is one MACHINE on the tapes of its word layout (`wenc`), built from compiled word programs and
docked machines, with the same entry, exit and costs:

* **`SeedsWS`** (BridgeT's input): `SeedsWM` with the program replaced by a machine `M` on the `L.ns + 2 + L.nr` tapes
  of the layout, and the run a `Step` of `M` from `wenc` of every `SdEntry` state to `wenc` of the exit state;
* **`SeedsWM.toWS`**: a word-level S4 is a machine-level one (the compiled program, `WExec.exec`, `Exec.step`).

Paper quantities: the printed numerator `fpNum = Σ_c Σ_e Σ_ℓ M·Σ R̂` and denominator (P3:3044-3048), the seeds
phase's cost `|E|·tab + (|centers|·|E|·Q)·pt + ov`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Split
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
