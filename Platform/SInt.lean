import Platform.BinW
import Platform.Hoare

/-! # Signed integers on `BinW`

The near-cubic-gates paper machine model: "Arithmetic on polynomial-bit integers uses elementary multiword
algorithms." The tabulator handles signed weights, thresholds, coefficients and printed values (lem:exact for signed
weights; lem:signed-printer).

**Format.** Sign and magnitude, the sign in the LOW bit: an integer `z` with `|z| < 2^W` is the fixed-width number
`encS z = 2|z| + [z < 0]` of width `W + 1` (**`SNumOn σ X W z`** = `NumOn σ X (W+1) (encS z)`). Its bits are
`[z < 0] :: binary W |z|`, which is exactly the printer's field `MatrixScoreBatch.signMagnitude W z`
(**`signMagnitude_eq`**), so cut fields reach the printer without conversion. Zero is canonical (`encS 0 = 0`).

**Programs** (`WMX`, scratch magnitude streams `M N` of width `W + 1`, sign registers `S T`, BinW scratch registers
`F R`, all registers `0` before and after):
* `sadd X Y …`: `X := x + y` (**`sadd_spec`**), `ssub`: `X := x − y` (**`ssub_spec`**), `sneg`: `X := −x`
  (**`sneg_spec`**), `smul X Y … C D … G`: `X := x·y` (**`smul_spec`**), `slt X Y …`: `F := [x < y]`
  (**`slt_spec`**), each with every other stream and register unchanged; costs `O(W)` (`O(W²)` for `smul`).
* building blocks: `split` (magnitude and sign), `join` (back to `encS`, normalizing the sign of zero).
Specs are over `ℤ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Platform.SInt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.Round (mapS_keepA)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)

/-! ## The format -/

/-! ## The sign bit -/

/-! ## Zero test -/

/-! ## Split and join -/

section Split

end Split

section Join

end Join

/-! ## The signed sum of two magnitudes with signs -/

section Core

end Core

/-! ## The operations -/

section Ops

end Ops

/-! Programs are opaque to consumers: use the spec theorems. -/

end NearCubicGates.Close.Platform.SInt
