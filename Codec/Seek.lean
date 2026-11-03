import Codec.FieldCircuit
import Codec.Copy
import Codec.Circuit

/-!
# W3b, part 2: seeking a transcoded circuit

The worker transcodes every guessed circuit once (W3a, `circuitW`) to a stream `CW` holding
`marks (circuitWord C_0) ++ marks (circuitWord C_1) ++ …`. A call needs circuit `i` in J3's codec: `seekCircuits`
skips the first `i` words (`skipCircuit`, marked encoding), then `copyCircuit` appends `marks (circuitWord C_i)` to
the call stream.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Joins

variable {ns nr : ℕ} (cap : ℕ)

/-- The marked circuit words of the first `i` circuits. -/
def cwPrefix {q : ℕ} (Cs : ℕ → NCircuit q) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun j => marks (circuitWord (Cs j))

end NearCubicGates.Close.Codec
