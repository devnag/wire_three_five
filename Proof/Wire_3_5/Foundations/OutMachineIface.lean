import Lean
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.UnionMachine.RegRatOps
import Proof.Wire_3_5.Foundations.OutMachineIfaceBase


noncomputable section
set_option maxRecDepth 4096


/-! # X6: the out machine's word program, phase interface

"At each of `2^{n-k}` columns, evaluate the reported lookup at these `Q` pairs and sum it" (P3:3046-3047); "At one
sampled input, [...] This takes polynomial time without evaluating a monomial expansion" (P3:3175-3178). The final
pass prints its sum as the reduced rational `ratWord (Num/Den)` (`Seams.OutMachine2`, P3:3044-3048) from `Num`, `Den`
in `W`-bit binary, within `C·(W+1)^2` steps: a binary gcd, not a value-linear one.

The out machine is ONE word program (`WM nsO nrO`, FinalPass `Tm`) `P1 ; P2 ; P3 ; P4 ; P5 ; P6`, composed by
`WExec.seq` (cost `n + 1 + k`), lifted ONCE to a machine by base's masked reset (`C4KW.wm_blankR`, cost `2n + 2`)
and docked by `Block.dockKeep` onto `o`, `tN`, `tD` and the room (`mOut = 21` tapes: the cell, nine scratch streams,
ten registers, the log).

* **Layout**: streams `sO` (the output, blank until P5), `sN`, `sD` (the inputs), `sU`, `sV` (the gcd pair), `sT`
  (the swap temporary), `sX j` (`j < 6`, P4/P5's words); registers `rF`, `rR` (a pass's flag and counter, as in
  `RegRat`), `rW` (`= W` from P1 to P6), `rK` (a loop counter), `rg j` (`j < 6`, scratch). Every phase runs at the
  register bound `capO W = 8W + 8`.
* **Boundary predicates**: `Entry` (the machine's entry), `Bd` (heads `0`, cell `false`, registers `0` but `rW = W`),
  `Words` (P1–P4: `N, D, U, V` are `W`-bit words, `T` a `W`-bit word, the six room words `0`, `O` blank), `Quot`
  (P4 → P5: the reduced pair on `sX 0`, `sX 1`), `Printed` (P5 → P6: `O = ratWord q`).
* **Phases** (each: a program, its cost, a PLAIN constant `C` with `cost W ≤ C·(W+1)^2`, its run): `Ph1` (count `W`,
  make the room words, strip the common factors `2`: `strip W num den`), `Ph2` (`U := oddPart W b`, `V := a`), `Ph3`
  (constant-time Stein, `2W` rounds: `U := gcd u v`, `V := 0`), `Ph4` (the exact divisions `a/g`, `b/g`), `Ph5` (the
  print), `Ph6` (clear `rW`; **`ph6`** is proved here).
* **`ratWord_coprime`**: for coprime `n`, `d > 0`, `ratWord (n/d) = false :: natWord n ++ natWord d` (P5's print
  encoding, checked against the actual `ratWord`).
* **`OutOfPhases`**: the assembly's statement (`Ph1 → … → Ph6 → Bank.OutGen mOut`).

Paper quantity of the main types: the printed rational `ratWord (Num/Den)` (P3:3044-3048) and its reduced numerator and
denominator (`strip`, `oddPart`, `Nat.gcd`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

/-! ## The layout -/

/-! ## The boundary predicates -/

/-! ## The values -/

/-! ## The phases -/

/-! ## The assembly's statement -/

/-- **The out machine's assembly**: the six phases give the out machine's target `Bank.OutGen mOut`. -/
abbrev OutOfPhases : Type := Ph1 → Ph2 → Ph3 → Ph4 → Ph5 → Ph6 → Bank.OutGen mOut

end NearCubicWires.WireExponent3_5.FinalPass.Out

end
