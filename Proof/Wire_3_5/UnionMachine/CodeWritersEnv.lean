import Proof.Wire_3_5.UnionMachine.CodeWriters

/-! # C6 front, U5: the carrier-envelope writer's interface (extends the code writers)

Every call of `(tr:tests)` must meet `lem:primitive`'s precondition (P3:3083-3094): its named carriers lie within the
fixed description envelope, "at most `(n+1)^deg` atom occurrences, each with at most `(n+1)^deg` description bits"
(`Stars.Carrier.WithinEnvelope`). A guessed atom is unbounded, so the union machine checks each named carrier
physically: the carrier of a variable is the gates of its grid atoms and parity (`CodeWriters.carrierOf`), the
envelope bit is decided on those gates. Like the carrier-code writer, this writer reads the atoms' codes.

* **`EnvWriter m deg`** (`env_ready`): from `u = natWord q ++ codesWord m cs`, the one-bit word
  `[decide ((carrierOf m cs).WithinEnvelope deg)]`.

Paper quantity of the main type: the envelope bit of a call's named carrier. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairRepresentation (natWord)

end NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters
