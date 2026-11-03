import Lean
import Proof.Wire_3_5.FinalPass.SeamsProg
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.S5SeamBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2: the S5 sub-seam — the front's two halves and how they compose to `FrontOut`

The final pass's front phase (S5, `PlanFP.FpPhases.front`) runs from `fpEntry` (the framed input `fpIn` on tape `0`,
every other tape blank) to a bank meeting the `Seams.FrontOut` at `Seams.frontWords`. It is
split in two machines run in sequence, each on its own tapes of one common layout:

1. **the THR half** (THR2, **`S5Thr`**) runs FIRST. It writes the THR slots `8 … 15` of `frontWords` (for a SYM
   request, or off the star hypotheses, they stay `[]`), uses only its scratch tapes `thrSc` (register tapes of
   the layout), leaves them blank of length at most `len r ≤ Kc·(|fpIn|+1)^{Dc} + 1`, keeps every other tape, and
   returns every head to `0`.
2. **the core half** (PA2, **`S5Core`**) runs SECOND, from the THR half's exit (`ThrExit`): the input on tape `0`, the
   THR slots written, its own slots and scratch blank, the THR scratch blank of length `≤ Kc·(|fpIn|+1)^{Dc} + 1`. It
   writes S4's slots `0 … 7` (`s4Core`) and the SYM slots `16 …` (`E3`'s words and numbers), the numbers `Num = 0`,
   `Den = fpDen` in `W`-bit binary on `tN`, `tD` (`W` its choice, `ptCount·vmax < 2^W`; for a THR request it reads
   `|𝒢|` and the primes from the THR slots `15`, `13`), and blanks every other tape to exactly S4's register length
   (`Kc·(|fpIn|+1)^{Dc} + 1` on register tapes, `0` elsewhere): `FrontOut` at `frontWords`.

* **`S5Lay`**: the layout (S4's `t`, `wd`, `tN`, `tD`, `reg`, `Kc`, `Dc`; the halves' scratch sets), with the facts the
  halves need: tape `0` is a register tape (a machine cannot shrink a tape, and `FrontOut.blank` asks for exact
  lengths), the scratch tapes are register tapes off the word and number tapes, the two scratch sets disjoint;
* **`S5Thr L`** (THR2's half), **`ThrExit`** (its exit, the core's entry), **`S5Core L`** (the half).

Paper quantity of the main types: the front's words `Seams.frontWords` (S4's words and the per-point evaluators'
call words, P3:3046-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch

section Family

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam

end
