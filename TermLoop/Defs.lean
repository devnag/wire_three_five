import Setup.Entry
import CheckedPCPP.WMXReady
import Codec.Unframe
import Bindings.Williams14_Corollary4_4
import Counter.Window
import Joins.Counter
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NearCubicGates.FiniteAverages
import NearCubicGates.PublishedSources.PrimeDensity
import NearCubicGates.PublishedSources.Witness
import Proof.Circuits.CanonicalWitnessCodec
import Proof.Foundations.ThresholdDAGCompilation
import Std
import Target
import Worker.Calls
import Worker.Format
import Worker.Meaning
import WorkerArith.VerdictVal
import Codec.FieldGate
import Worker.TermModelLink
import CheckedPCPP.ClauseFront
import WorkerArith.Classes

/-!
# W3d: the worker's term loop (statements `LoopIter`, `gadget_ideal`, `termLoop_ideal`)

The near-cubic-gates paper's fixed weak machine and 2374–2392: for every gadget `a < M` the worker reads clause `a mod 2^{rb}` of
the three-query PCPP's clause list, forms the ten terms of the gadget (`Worker.Guess.operands`: the helper, the three
literals, the three literal pairs, the three literal–helper pairs), and appends for each term its flip and its raw
interval to the I-stream (an exact parity mean, or one counter call on the term's witness field). After the `M`
gadgets the I-stream is closed: it is then `frame (verdictWord (verdictReq …))`, the request of the verdict machine.

`LoopIter i` is the state after `i` gadgets: `LoopEntry` with the entries of gadgets `< i`
appended to the I-stream `VI` (head and `R 9` at its end), the witness stream's head at witness field `10 i`, the
gadget index `rA = i` and the loop counter `rLC = M − i`.

The gadget body `gadgetW` (registers `48 … 74`, zero outside the body):
* the clause front end (`frontW` on the J8 word stream, `R 0 = rA`, `R 1 … R 17` = registers `48 … 64`):
  variables `V k` (`48 … 50`), signs `S k` (`51 … 53`), `proofBits` (`54`), `randomBits` (`55`);
* the classification of the three literals (`ltSubW V k` against `rSC`): `Dk = V k − sysCount` (`66, 68, 70`),
  `Fk = sysCount − V k` (`67, 69, 71`; `≠ 0` iff systematic), scratch `72, 73`;
* per term `t = 0 … 9`, in `Worker.Guess.operands` order: load the operands into `R 0 … R 5`
  (`loadLit` / `loadHelper` with the helper index `rPB + rA`, scratch `74`), run `termW1` / `termW2`, clear
  `R 0 … R 5`;
* clear the gadget registers; `rA := rA + 1`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Joins
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd)

noncomputable section

/-! ## Witness fields -/

/-! ## The loop data -/

section Data

/-! ## Operand descriptors and counter budgets -/

end Data

/-! ## The states -/

section States

end States

/-! ## The program -/

section Program


end Program

/-! ## Hypotheses, costs, statements -/

section Statements

end Statements

end

end NearCubicGates.Close.TermLoop
