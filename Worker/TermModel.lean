import Bindings.Williams14_Corollary4_4
import CheckedPCPP.LitDecode
import Codec.CallPairW
import Codec.Transcode
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
import WorkerArith.SuppEqDefs
import WorkerArith.Entries

/-!
# W3d: the term model (the interface for the term programs)

An operand descriptor `Opd` is what the machine holds in registers for one operand: its flip, whether it is
systematic, and its index (the coordinate `u`, or the auxiliary name `j`). `model1`/`model2` are the entries (flip,
raw interval) that the term programs append, stated over the machine's data only:
- the circuit family `Cs` (the transcoded `circAt`);
- the support rows `rows` (the supports record);
- `q`, the counter `ctr`, the radius `ω` and the witness field `w`.

`termParts_model1`/`termParts_model2`: for the decoded guess these ARE `Guess.termParts` of the operand atoms,
under the identifications `Cs j = G.circuits j` at the named circuits and `rows j` = the canonical code-support row
`j` for `j < code length`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Joins NearCubicGates.Close.Codec
open NearCubicGates.Close.WorkerArith (sysList halfIf)

/-- An operand in registers: flip, systematic?, index. -/
structure Opd where
  neg : Bool
  sys : Bool
  idx : ℕ

section Model
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) {q : ℕ} (Cs : ℕ → NCircuit q) (rows : ℕ → List ℕ) (ω : ℚ)
  (w : List Bool)

/-- **The entry of a one-operand term.** -/
noncomputable def model1 (o : Opd) : Bool × (ℚ × ℚ) :=
  if o.sys then (o.neg, (halfIf (decide (sysList q rows o.idx ≠ [])), 0))
  else (o.neg, ctr.value (oneCallOf Cs o.idx [] ω) w)

/-- **The entry of a two-operand term.** -/
noncomputable def model2 (o1 o2 : Opd) : Bool × (ℚ × ℚ) :=
  match o1.sys, o2.sys with
  | true, true => (xor o1.neg o2.neg, (halfIf (decide (sysList q rows o1.idx ≠ sysList q rows o2.idx)), 0))
  | true, false => (xor o1.neg o2.neg, ctr.value (oneCallOf Cs o2.idx (sysList q rows o1.idx) ω) w)
  | false, true => (xor o1.neg o2.neg, ctr.value (oneCallOf Cs o1.idx (sysList q rows o2.idx) ω) w)
  | false, false =>
    (xor o1.neg o2.neg, if o1.idx = o2.idx then (0, 0) else ctr.value (pairCallOf Cs o1.idx o2.idx ω) w)

end Model

end NearCubicGates.Close.Worker
