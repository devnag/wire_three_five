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

/-!
# W3e, value level: what the verdict machine computes (the near-cubic-gates paper's eq:gadget-upper,
its guards, and eq:gadget-acceptance)

* `nats r`: the request word is a concatenation of `natWord`s (`verdictWord_eq`); a term contributes seven fields
  (flip bit, then sign, magnitude and denominator of `p̂` and of `κ̂`).
* The common denominator is `D = 2^L`, `L = |verdictWord r|` (not `2^{q+1}`, which has exponentially many bits in
  `L`): every endpoint denominator divides `2^{q+1}` (`hden`), so it is a power of two, and it is below `2^L`.
* The sum `Σ (σ_t (flipI x).1 + (flipI x).2)·D` is kept as two naturals `POS − NEG` (`posS`, `negS`,
  `sum_eq_pos_sub_neg`).
* **`upper_test`**: `upperL M I < γ − εT ⟺ (e + c⁻)·Y + e·POS < c⁺·Y + e·NEG` with `γ − εT = c/e`,
  `Y = 2·max M 1·D`. **`guard_test`**: `γ < εT·N^{10} ⟺ A + B·N^{10} < C + D'·N^{10}` (naturals from the signs).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Worker
open NearCubicGates.Close.Joins (listWord bitWord outputWord ratWord)

/-! ## The word as naturals -/


/-! ## Field access -/

/-! ## Bounds -/

/-! ## Endpoints over the common denominator -/

/-! ## Contributions: the sum as `POS − NEG` -/




end NearCubicGates.Close.WorkerArith
