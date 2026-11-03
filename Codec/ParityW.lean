import Codec.CallPairW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Joins

variable {ns nr : ℕ} (cap : ℕ)

/-! ## A code-parity row of the supports record -/

/-- The marked words of the first `r` rows (`listWord natWord (rows j)`). -/
def rowPrefix (rows : ℕ → List ℕ) (r : ℕ) : List Bool :=
  (List.range r).flatMap fun j => marks (listWord natWord (rows j))

end NearCubicGates.Close.Codec
