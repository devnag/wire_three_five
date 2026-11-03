import WorkerArith.RowTest
import Codec.FieldGate
import CheckedPCPP.WMXReady
import Codec.Unframe

/-!
# W3dl, piece 2: do two systematic coordinates have the same parity support? (`suppEqW`, programs + statement)

The two-parity term `[sys u, sys v]` has raw mean `parityMean (symmDiff S_u S_v)` (the near-cubic-gates paper), i.e. `1/2`
iff `S_u ≠ S_v` (`symmDiff_nonempty_iff`). With canonical lists, set equality is word equality (`canonList_inj`).
`suppEqW` writes the canonical list of each coordinate to a scratch stream (`Codec.parSys` for `u < q`,
`Codec.parRow` for row `u − q` of the supports record), compares the two marked words cell by cell, blanks both
scratch streams and rewinds the record.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Joins (listWord)

variable {ns nr : ℕ}

/-- The canonical parity list of systematic coordinate `u` (`q` outer coordinates, then the code rows). -/
def sysList (q : ℕ) (rows : ℕ → List ℕ) (u : ℕ) : List ℕ := if u < q then [u] else rows (u - q)

end NearCubicGates.Close.WorkerArith
