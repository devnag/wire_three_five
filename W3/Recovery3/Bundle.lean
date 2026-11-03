import W3.Joins.Cases
import OuterM.Width
import CheckedPCPP.Harness
import GR.Aliases
import Proof.Foundations.SourceRegistry
import Proof.MachineModel.ClockJoin

/-!
# The narrow bundle: the wires twins of the gates `GateSources`/`GateParams` API

The near-cubic-wires paper, Lemma C.10: the recovery reads only the substituted outer verifier at `mw SV` (Fact C.1, the
succinct verifier), the hierarchy/refuter, the amplifier, and the three canonical choices of (
`Joins/Cases.lean`). The gates recovery (`Recovery.After*`, `Recovery.Common*`, `ENP.UInst`) reads exactly these through
`s : GateSources`, `g : GateParams` (`s.mw`, `g.sv s`, `s.hierarchy`, `s.amplification`, `g.width s ν`, `g.SrcExists`,
`g.firstSrc`, `g.IsCaseTwo`, `g.selectedPair`, `g.matchPCP`, `g.gateCore`, …). Following the gates GR precedent (a
narrow bundle with the same accessor names, `GR.Bundle`), `WS` carries the fixed wires objects
`(S, k, clock, mw, L, SV)` and `WP` the numeric parameters `(G, d_G, K_amp, onset)`; every accessor is a reducible
wrapper of the definition at `s.mw s.SV`, and `WP.gateCore` is `coreC` (the hard slice) — so the ported
after-prefix program prints `coreC`, the language's value. `positionLog` is fixed to `1`: `m(q) = K_amp(q + d + 1)` is
`widthAtC` (C.12), GR's `widthAt` at `ext = 0`.
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.LocalBitMultitape
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close NearCubicWires.Bindings.CLW20Lemma311

namespace W3.Recovery3

namespace WP

open W3.NearCubicWires.RepairSource

end WP

/-! ## The width as GR's `WidthSource` (gates `Recovery/GateWidth.lean` at `mw SV`) -/

end W3.Recovery3
