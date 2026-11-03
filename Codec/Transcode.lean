import Codec.FieldCircuit
import Codec.Seek

/-!
# W3c, part c5: transcoding every guessed circuit

`transcodeW` runs `circuitW` (W3a) `m` times (`C = m` counts down): from the reading head of `W` at `p0`, the stream
`o` gains the marked J3 words of the `m` successive circuit fields (`cwPrefix`, the stream `CW` that `callPairW` /
`callOneW` read), the head of `W` ends after the last field. The `j`-th circuit is the one `Worker.decodeGuess` reads
(`readCircuit` at the `j`-th position).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-- The position of the `j`-th circuit field. -/
def circPos (w : List Bool) (q p0 : ℕ) (j : ℕ) : ℕ := iter (fun p => circuitEnd w p q) p0 j

/-- The `j`-th decoded circuit. -/
def circAt (w : List Bool) (q p0 : ℕ) (j : ℕ) : Joins.NCircuit q := (readCircuit q (w.drop (circPos w q p0 j))).1

end NearCubicGates.Close.Codec
