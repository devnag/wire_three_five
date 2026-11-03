import WorkerArith.CallTailMain
import WorkerArith.RowTest
import WorkerArith.SuppEq
import Worker.TermModel
import Codec.FieldGate
import Codec.ParityW

/-!
# W3dl: the per-term programs (programs + statements `termW1_ideal`, `termW2_ideal`)

The near-cubic-gates paper: "every nonexact term is a single-circuit, pair-XOR, or circuit-XOR-raw-parity call. Pure
parity terms, constants, and repeated-coordinate identities are evaluated exactly." A term program reads its operands
from registers (flip `≠ 0`, systematic `≠ 0`, index), consumes one witness field, and appends
`marks (bitWord f ++ outputWord raw)` to the I-stream, `(f, raw) = Worker.model1/model2` (Worker/TermModel.lean).

Register file `R : Fin 40 ↪ Fin nr`:
`R 0, R 1, R 2` = operand 1 (flip, systematic, index); `R 3, R 4, R 5` = operand 2; `R 6 = q`; `R 7` = a bound on the
circuit stream's prefix; `R 8` = a bound on the supports record's prefix; `R 9` = the I-stream's output position;
`R 10 … R 39` scratch (zero before and after).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Joins (Counter Call callWord outputWord bitWord ratWord NCircuit)
open NearCubicGates.Close.Worker (Opd model1 model2)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix)

/-! ## Register layout -/




/-! ## The streams -/

/-! ## Programs -/

section Programs

end Programs

/-! ## The ideal end state, the cost class, the hypotheses -/

section Budgets

end Budgets

end NearCubicGates.Close.WorkerArith
