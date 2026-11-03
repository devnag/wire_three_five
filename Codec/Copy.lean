import Codec.Circuit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Joins

variable {ns nr : ℕ} (cap : ℕ)

theorem marks_length (w : List Bool) : (marks w).length = 2 * w.length := by
  induction w with
  | nil => simp [marks]
  | cons b w ih => simp [marks] at ih ⊢; omega

end NearCubicGates.Close.Codec
