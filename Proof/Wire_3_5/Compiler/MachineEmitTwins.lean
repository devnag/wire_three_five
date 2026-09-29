import Proof.Wire_3_5.Compiler.MachineEmitRun

/-! # C3.6/C3.7: a twin of one emitted occurrence (P3:1929-1936, 1728-1731)

Paper: "Each resulting conjunction contains at most `Q'd` equation atoms, so Lemma alg:stack turns it into one separated
equation" (P3:1934-1936), printed as "the two successor cuts" (P3:1728-1731). The pool of MC7's twin (`cuts_twin`) as
C3a's pool children over two coordinates (coordinate 0 on the left, coordinate 1 on the right, no flips): the children
`x_L − x_R = 0`, `2x_L = 1` and `3x_R = −1`. At `h = 2` (`H = 4`), the union of labels `{1, 2}` (mask `6`, size `2`)
of a group with coefficient `3` and odd parity is written by the emit machine's entry word `entryOut` as the two
successor cuts of the stacked cut with left weight `2 + 4·0`, right weight `0 + 4·3`, target `1 + 4·(−1)` and
coefficient `3·(−2)`, the third cut of `cuts_twin`. The paper quantity is the request's cut words of one occurrence.
Main declarations: `twinSide`, `twinPC`, **`entry_twin`** (`decide`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut cutWord)

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
