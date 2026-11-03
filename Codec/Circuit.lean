import Joins.Counter
import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Primitive.Writers.ParseNat

/-!
# J3 codec readers, part 3: moving past integer lists, gates, bit lists and circuits

`skipIntList` (`listWord intWord`), `skipGate` (`gateWord g = listWord intWord (ofFn g.weight) ++ intWord threshold`),
`skipBitList` (`listWord bitWord`), `skipGateList` (`listWord gateWord`) and `skipCircuit` (`circuitWord C =
listWord gateWord gates ++ listWord intWord coeffs ++ listWord bitWord table`). All scratch registers are `0` again at
the end; only the head of the stream moves.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.Joins

variable {ns nr : ℕ} (cap : ℕ)

local notation "E" => WireExponent3_5.PrimAsm.ParseNat.enc
local notation "S" => WireExponent3_5.PrimAsm.ParseNat.stp

end NearCubicGates.Close.Codec
