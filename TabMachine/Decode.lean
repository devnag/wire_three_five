import Platform.SInt
import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.FinalPass.FiltTabRef

/-! # K5 back end, part 1: decoding the printer's table (M6)

The near-cubic-gates paper lem:signed-printer prints the signed table exactly; proof 1's printer
(`CompetitorCountTable.cold_run`) leaves the table's residues modulo `2^q` as raw `q`-bit words, row-major
(`CompetitorFinalTable.word q odd f`). Plan M6: "two's complement recovers the exact integer". An entry `v < 2^q`
is the residue of the integer **`tc q v`** (`= v` if `v < 2^{q-1}`, else `v − 2^q`); when the printed integer has
magnitude below `2^{q-1}`, `tc q v` IS that integer (`tc_residue`).

**`decode`** reads `N` raw `q`-bit entries and appends, for each, the signed record `binary (q+1) (encS (tc q v))`
(sign-magnitude format, `Platform.SInt`) to a fresh output stream, closing it as a record stream
(**`decode_spec`**). It needs no arithmetic: the sign is the entry's top bit (read ahead, `peek`), and the magnitude
`2^q − v` of a negative entry is streamed low bit first by the two's complement rule "copy up to the first one, then
invert" (`xb`, **`xb_true_binary`**). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append appendO_nil)

/-! ## Two's complement -/

/-! ## The programs -/

/-! ## Specs -/

section Specs


end Specs

end NearCubicGates.Close.TabMachine
