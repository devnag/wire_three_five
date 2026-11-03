import Setup.CompSpec
import Bindings.Williams14_Corollary4_4
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
import WorkerArith.TermDefs
import WorkerArith.Classes

/-!
# W3c: the worker's set-up phase — the loop-entry state and the statement `SetupSpec` ((a′) form)

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer): on a source input `z` of length `N` the weak machine rejects unless `N = 2^ν`,
computes the native width `q`, reads the guessed pair `B = (B_src, B_pf)` (rejecting malformed descriptions), checks
`B_src(bin_ν(i)0^{q−ν}) = z_i` for every `i < N` (eq:source-check) and that `⟨B_src⟩_ν` has at most `L_ν` bits,
constructs `C^O_{⟨B_src⟩_ν}` with the imported constructor, substitutes `O_{B_pf}` for its oracle gates and negates
(`D_B`), applies the three-query PCPP, repeats the clause list to `M = 2^{⌈d_G lg(q+2)⌉}` clauses, and reads one circuit
per auxiliary name; the witness prefixes of the counter calls follow. The guess is read from the first `⌊N/16⌋`
witness bits.

`setup` runs from proof 1's cold start (`Verifier.inputTapes`: stream `0` = `frame x`, stream `1` = `frame bits`) to
the LOOP-ENTRY state of the term loop (W3d), `LoopEntry`, or rejects (`N < N0`, or `Worker.Format.setupFlag` is false:
a circuit field does not decode or a set-up guard fails, so `Format.verdict` is false).

Layout (`nrW = 128` registers, `nsW D + 1` streams):
* streams `0 X` (`frame x`), `1 BW` (`frame bits`), `2 WT` (the guess word), `3 CW` (transcoded circuits), `4 VI`
  (the I-stream), `5 S1`, `6 S2`, `7 TL`, `8 G`, `9 L` (`TermEnv` scratch and log), `10 … 15` spare (blank); then the block of the set-up's donors before the composite (`aB`, `tA` tapes:
  width, decoders, CHECK, the imported constructor; the set-up's flag `FL` is its slot `flag`), the composite (`kB`), the counter (`cB`, `tc` tapes,
  blank) and a blank tail of `46` streams. The J8 word stream `J` and the supports record `SUP` are the composite's own
  output tapes.
* registers `0 … 39` = `TermEnv.R` (`R 6 = q`, `R 7 = |CW|`, `R 8 = |rows prefix|`, `R 9` = VI's output position),
  `40 N`, `41 M`, `42 rb`, `43 cl`, `44 sysCount`, `45 a` (gadget index, `0`), `46` the loop counter (`M`),
  `47 proofBits`; every other register `0`.
* The I-stream header carries the precision base `b = ν^{lenRoot+1}` in its `N` field (`L_ν = b^{10}`), which the
  verdict machine reads for the guard `γ/L_ν < ε`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Joins
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)

noncomputable section

/-! ## The set-up data -/

/-- The sizes the loop entry holds (they bound the term loop's work). -/
noncomputable def setupSizeOf (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (N0 : ℕ) {N : ℕ}
    (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)) : ℕ :=
  let w := Codec.prefixBits bits (N / 16) ++ List.replicate pad false
  let p0 := 2 * (Worker.Format.readCount w).1 + 1
  let p1 := p0 + 2 * (Worker.Format.readCount (w.drop p0)).1 + 1
  N + pad + N0 + width s g N + gadgets s g N + ((pcpp s P g x B).proofBits + gadgets s g N) +
    (pcpp s P g x B).randomBits + (pcpp s P g x B).word.length + (supportsWord P.code (width s g N)).length +
    (Codec.cwPrefix (Codec.circAt w (width s g N) p1) ((pcpp s P g x B).proofBits + gadgets s g N)).length +
    (mwWord s g N B.src).length + (PCPPNative.descriptor B.src).length + (PCPPNative.descriptor B.pf).length +
    Worker.nu N ^ (g.lenRoot + 1)

/-- What the set-up is built from: the composite (exact form), the tape count `tA` of the set-up's donors before the
composite, the counter's tape count (the counter block is blank at loop entry), the input-length
guard `N0` (past it, `q ≥ 2` and `|q.bits| ≤ N + 1`), and the set-up's capacities and costs, with the loop
entry's sizes below the cost. -/
structure SetupData (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  cf : CompFull s P g
  tA : ℕ
  /-- The set-up's flag slot in its donor block (`Worker.Format.setupFlag`). -/
  flag : Fin tA
  tc : ℕ
  N0 : ℕ
  hN0 : ∀ N, N0 ≤ N → 4 ≤ N ∧ (width s g N).bits.length ≤ N + 1
  /-- The register capacity of the common prefix (before the flag). -/
  capA : ℕ → ℕ → ℕ
  /-- The register capacity the set-up needs. -/
  setupCap : ∀ {N : ℕ}, BitInput N → List Bool → ℕ → Outer.OuterGuess (width s g N) → ℕ
  /-- The cost of the rejecting runs. -/
  rejectCost : ∀ {N : ℕ}, BitInput N → List Bool → ℕ → ℕ
  /-- The cost of the set-up to loop entry. -/
  setupCost : ∀ {N : ℕ}, BitInput N → List Bool → ℕ → Outer.OuterGuess (width s g N) → ℕ
  sizeLe : ∀ {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)),
    setupSizeOf s P g N0 x bits pad B ≤ setupCost x bits pad B

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- The number of streams minus one (the last `46` streams: a blank tail block, room for the verdict machine's work
tapes at the loop exit). -/
def nsW (D : SetupData s P g) : ℕ := 15 + D.tA + D.cf.t + D.tc + 46

/-- The number of registers. -/
abbrev nrW : ℕ := 128

/-! ## Streams -/

section Streams
variable (D : SetupData s P g)

def fixS (i : ℕ) (h : i < 16) : Fin (nsW D + 1) := ⟨i, by unfold nsW; omega⟩

def sX : Fin (nsW D + 1) := fixS D 0 (by decide)
def sBW : Fin (nsW D + 1) := fixS D 1 (by decide)
def sWT : Fin (nsW D + 1) := fixS D 2 (by decide)
def sCW : Fin (nsW D + 1) := fixS D 3 (by decide)
def sVI : Fin (nsW D + 1) := fixS D 4 (by decide)
def sS1 : Fin (nsW D + 1) := fixS D 5 (by decide)
def sS2 : Fin (nsW D + 1) := fixS D 6 (by decide)
def sTL : Fin (nsW D + 1) := fixS D 7 (by decide)
def sG : Fin (nsW D + 1) := fixS D 8 (by decide)
def sL : Fin (nsW D + 1) := fixS D 9 (by decide)

/-- The composite's block. -/
def kB (j : Fin D.cf.t) : Fin (nsW D + 1) :=
  ⟨16 + D.tA + j.val, by have := j.isLt; unfold nsW; omega⟩
/-- The counter's block (blank at loop entry). -/
def cB (j : Fin D.tc) : Fin (nsW D + 1) :=
  ⟨16 + D.tA + D.cf.t + j.val, by have := j.isLt; unfold nsW; omega⟩


end Streams

/-! ## Registers -/

abbrev rN : Fin nrW := 40
abbrev rM : Fin nrW := 41
abbrev rRB : Fin nrW := 42
abbrev rCL : Fin nrW := 43
abbrev rSC : Fin nrW := 44
abbrev rA : Fin nrW := 45
abbrev rLC : Fin nrW := 46
abbrev rPB : Fin nrW := 47

/-! ## The guess word and its decoded data -/

/-- **The guess word**: the first `⌊N/16⌋` witness bits (blanks past the end of `bits`), then `pad` blanks. The
machine copies only the first `⌊N/16⌋` bits; the blanks are not written (every stream reads blank past its end), so
`pad` is a free parameter of the ideal state, chosen by the consumer so that every field it reads is physical. -/
def guessWord (N : ℕ) (bits : List Bool) (pad : ℕ) : List Bool :=
  Codec.prefixBits bits (N / 16) ++ List.replicate pad false

/-- The position after one circuit field (`readField`: a unary count `ℓ`, then `ℓ` bits). -/
def oracleEnd (w : List Bool) : ℕ := 2 * (Worker.Format.readCount w).1 + 1

section Decoded

end Decoded

/-! ## The loop-entry state -/

section Entry
variable (D : SetupData s P g)

/-- The cold start (proof 1's `Verifier.inputTapes`): `frame x` on stream `0`, `frame bits` on stream `1`, every
other stream blank, every head and register `0`, the result cell `false`. -/
def coldState (xs bits : List Bool) : WState (nsW D) nrW where
  st := fun i => if i = sX D then RepairOrdinary.frame xs else if i = sBW D then RepairOrdinary.frame bits else []
  sh := fun _ => 0
  val := fun _ => 0
  cell := false

end Entry

/-! ## Sizes, capacity and cost -/

section Cost

end Cost

/-! ## The statement -/

end

end NearCubicGates.Close.Setup
