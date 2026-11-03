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
import Proof.MachineModel.OrdinarySignedSortKey

/-!
# The worker's witness format (W3): every bit string decodes to a guess

The witness word is read left to right; past its end every bit reads `false`, so EVERY bit string decodes to a
guess (`decodeGuess`) and the machine validates nothing. Fields:
* a count `k`: `1^k 0` (unary, so loops over counts are paid for by the witness itself);
* a bit field: a count `ℓ`, then `ℓ` raw bits;
* a natural number: a bit field read little-endian (`RadixSemantics.value`); the honest word of `x` is `1^L 0` then
  the `L = natBitLength x` low bits of `x`;
* an integer: a sign bit, then a natural number (`−0` reads as `0`);
* a gate on `q` inputs: `q` integers (weights), then an integer (threshold);
* a circuit: a count `k`, `k` gates, `k` integers (coefficients), a bit field (table).
The guess (the near-cubic-gates paper's fixed weak machine, (a′) repair): the codes of `B_src` and `B_pf` as natural numbers (proof 1's oracle field,
twice, each decoded by `decodeBooleanCircuit` exactly as proof 1's `WitnessOracleRun.cold_run` decodes it), then
`auxCount` circuits, then
the `10M` witness prefixes as bit fields (order `10a + t`). `verdict` is what the machine computes: both circuit fields
decode, and the decoded guess passes the test (`Guess.Certified`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.ExecutableInterfaces
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Joins NearCubicGates NearCubicGates.Close.Counter
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.CanonicalWitnessCodec

namespace Format

/-! ## Readers -/

/-- A unary count `1^k 0`. -/
def readCount : List Bool → ℕ × List Bool
  | true :: r => ((readCount r).1 + 1, (readCount r).2)
  | false :: r => (0, r)
  | [] => (0, [])

/-- `ℓ` raw bits (`false` past the end). -/
def readBits (ℓ : ℕ) (w : List Bool) : List Bool × List Bool :=
  (List.ofFn fun i : Fin ℓ => w.getD i.val false, w.drop ℓ)

/-- A bit field: a count, then that many bits. -/
def readField (w : List Bool) : List Bool × List Bool :=
  readBits (readCount w).1 (readCount w).2

/-- A natural number: a bit field, little-endian. -/
def readNum (w : List Bool) : ℕ × List Bool :=
  (value (readField w).1, (readField w).2)

/-- An integer: a sign bit, then a natural number. -/
def readInt (w : List Bool) : ℤ × List Bool :=
  (if w.headD false then -((readNum w.tail).1 : ℤ) else (readNum w.tail).1, (readNum w.tail).2)

/-- `n` items in a row. -/
def readMany {α : Type} (rd : List Bool → α × List Bool) : ℕ → List Bool → List α × List Bool
  | 0, w => ([], w)
  | n + 1, w => ((rd w).1 :: (readMany rd n (rd w).2).1, (readMany rd n (rd w).2).2)

/-- A gate on `q` inputs: the weights, then the threshold. -/
def readGate (q : ℕ) (w : List Bool) : NormalizedThresholdGate q × List Bool :=
  (⟨fun i => (readMany readInt q w).1.getD i.val 0, (readInt (readMany readInt q w).2).1⟩,
    (readInt (readMany readInt q w).2).2)

/-- A circuit: the gate count, the gates, as many coefficients, the table. -/
def readCircuit (q : ℕ) (w : List Bool) : NCircuit q × List Bool :=
  let k := readCount w
  let gs := readMany (readGate q) k.1 k.2
  let cs := readMany readInt k.1 gs.2
  (⟨gs.1, cs.1, (readField cs.2).1⟩, (readField cs.2).2)

theorem readCount_snd : ∀ w : List Bool, (readCount w).2 = w.drop ((readCount w).1 + 1)
  | [] => rfl
  | true :: r => by simp only [readCount, List.drop_succ_cons]; exact readCount_snd r
  | false :: r => rfl

/-- The rest after a field is the word after its `2ℓ + 1` bits. -/
theorem readField_snd (w : List Bool) : (readField w).2 = w.drop (2 * (readCount w).1 + 1) := by
  unfold readField readBits
  simp only [readCount_snd, List.drop_drop]
  congr 1
  omega

/-! ## Honest words -/

def countWord (k : ℕ) : List Bool := List.replicate k true ++ [false]
def fieldWord (b : List Bool) : List Bool := countWord b.length ++ b
def numWord (x : ℕ) : List Bool := fieldWord (binary (natBitLength x) x)

/-! ## Round trips -/

theorem readCount_word (k : ℕ) (r : List Bool) : readCount (countWord k ++ r) = (k, r) := by
  induction k with
  | zero => simp [countWord, readCount]
  | succ k ih =>
    have h : countWord (k + 1) ++ r = true :: (countWord k ++ r) := by
      simp [countWord, List.replicate_succ]
    rw [h, readCount, ih]

theorem readBits_append (b r : List Bool) : readBits b.length (b ++ r) = (b, r) := by
  unfold readBits
  refine Prod.ext ?_ (by simp)
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1)]
  simp [List.getElem?_eq_getElem h2]

theorem readField_word (b r : List Bool) : readField (fieldWord b ++ r) = (b, r) := by
  unfold readField fieldWord
  rw [List.append_assoc, readCount_word, readBits_append]

theorem lt_two_pow_natBitLength (x : ℕ) : x < 2 ^ natBitLength x := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem readNum_word (x : ℕ) (r : List Bool) : readNum (numWord x ++ r) = (x, r) := by
  unfold readNum numWord
  rw [readField_word]
  simp [binary_value _ _ (lt_two_pow_natBitLength x)]

end Format

open Format

/-! ## The guess -/

/-- A fixed oracle for undecodable codes (the machine rejects them, so it is never tested). -/
def defaultOracle (n : ℕ) : BooleanCircuit n where
  nodes := [.const false]
  output := ⟨0, by simp⟩
  wellFormed := by intro i; fin_cases i; trivial

section Guess
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)

/-- Both circuit fields decode (proof 1's decoder flag, once per circuit of the pair). -/
noncomputable def oracleOK (N : ℕ) (w : List Bool) : Bool :=
  (decodeBooleanCircuit (width s g N) (value (readField w).1)).isSome &&
    (decodeBooleanCircuit (width s g N) (value (readField (readField w).2).1)).isSome

/-- Both circuit fields of the word `w` decode, to the pair `B` (the set-up's decoders, the near-cubic-gates paper's fixed weak machine: "rejecting
malformed descriptions"). -/
def Decodes (q : ℕ) (w : List Bool) (B : Outer.OuterGuess q) : Prop :=
  decodeBooleanCircuit q (value (readField w).1) = some B.src ∧
    decodeBooleanCircuit q (value (readField (readField w).2).1) = some B.pf

/-! ## The verdict: what the worker machine computes -/

end Guess

end NearCubicGates.Close.Worker
