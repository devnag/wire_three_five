import Close.Sources
import Proof.Foundations.Semantics

/-!
# The counter specification (the near-cubic-gates paper, thm:pair-uniform)

Consumer: the gadget weak worker (the fixed weak machine), which calls the counter on guessed
normalized circuits and guessed witness prefixes. Everything below is quoted from v2:

* "A call asks for the acceptance probability of one class circuit C¹, of C¹ ⊕ C² for two class circuits, or of
  C¹ ⊕ PAR_Σ" — `CallKind`, `Call.predicate`, `Call.prob`.
* "A normalized call has total top weight W ≤ 2n⁴, hence at most G₀ bottom gates …, and integer bottom parameters
  of magnitude below 2^{B₀}. Each f^r is given as a table on [−W^r, W^r] ∩ ℤ" — `NCircuit`,
  `Call.Admitted`.
* "a rational requested radius n^{−B₁} ≤ β ≤ 1/16, whose encoding uses at most n^{B₂} bits".
* "The algorithm returns dyadic rationals (p̂, κ̂) with |p̂ − Pr[C(z) = 1]| ≤ κ̂" — `Counter.dyadic`.
* "Every witness gives a sound probability interval" — `Counter.sound`.
* "some polynomial-length witness gives radius at most β if W ≤ a β 𝒜₃(n) for a pair-XOR call … W ≤ a β 𝒜₁(n)"
  for the other two kinds — `Counter.complete`.
* "It runs within 2^n/n^{μ_n} steps, uniformly over the admitted inputs" — `Counter.fast`.
* "The algorithm uses no oracle and reads no guessed data beyond its witness" — the counter is a
  deterministic `WordFunction` on the pair (call word, witness word).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Joins

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- A normalized class circuit on `n` inputs: integer bottom gates, integer top coefficients, and the top function
as a table on `[−W, W]` (index `score + W`). -/
structure NCircuit (n : ℕ) where
  gates : List (NormalizedThresholdGate n)
  coeffs : List ℤ
  table : List Bool

namespace NCircuit
variable {n : ℕ}

def topWeight (C : NCircuit n) : ℕ := (C.coeffs.map Int.natAbs).sum

def score (C : NCircuit n) (z : BitInput n) : ℤ :=
  ((C.gates.zip C.coeffs).map fun gc => gc.2 * if gc.1.eval z then 1 else 0).sum

def eval (C : NCircuit n) (z : BitInput n) : Bool :=
  C.table.getD (C.score z + C.topWeight).toNat false

/-- Equal gate and coefficient counts, nonzero coefficients, a full table, parameters below `2^B`. -/
def WellFormed (C : NCircuit n) (B : ℕ) : Prop :=
  C.gates.length = C.coeffs.length ∧ (∀ a ∈ C.coeffs, a ≠ 0) ∧ C.table.length = 2 * C.topWeight + 1 ∧
    ∀ g ∈ C.gates, (∀ i, (g.weight i).natAbs < 2 ^ B) ∧ g.threshold.natAbs < 2 ^ B

/-- The empty circuit (no gates, constant table `false`). -/
def empty (n : ℕ) : NCircuit n := ⟨[], [], [false]⟩

end NCircuit

inductive CallKind
  | single
  | pair
  | parity
  deriving DecidableEq

/-- One call. `second` is used only by `pair`, `parity` (the index list Σ) only by `parity`. -/
structure Call where
  n : ℕ
  kind : CallKind
  first : NCircuit n
  second : NCircuit n
  parity : List ℕ
  radius : ℚ

namespace Call

def parityOf (c : Call) (z : BitInput c.n) : Bool :=
  (c.parity.map fun i => if h : i < c.n then z ⟨i, h⟩ else false).foldl xor false

def predicate (c : Call) (z : BitInput c.n) : Bool :=
  match c.kind with
  | .single => c.first.eval z
  | .pair => xor (c.first.eval z) (c.second.eval z)
  | .parity => xor (c.first.eval z) (c.parityOf z)

/-- The acceptance probability over the uniform cube. -/
def prob (c : Call) : ℚ :=
  ((Finset.univ.filter fun z : BitInput c.n => c.predicate z = true).card : ℚ) / 2 ^ c.n

/-- Total top weight `W`. -/
def W (c : Call) : ℕ := c.first.topWeight + c.second.topWeight

/-- `B₀ = 4n⌈lg(n+1)⌉`. -/
def B0 (n : ℕ) : ℕ := 4 * n * Nat.clog 2 (n + 1)

end Call

/-! ## The codec (both sides implement it) -/

def intWord (z : ℤ) : List Bool := natWord (if z < 0 then 1 else 0) ++ natWord z.natAbs
def listWord {α : Type} (f : α → List Bool) (xs : List α) : List Bool := natWord xs.length ++ xs.flatMap f
def bitWord (b : Bool) : List Bool := natWord (if b then 1 else 0)
def gateWord {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  listWord intWord (List.ofFn g.weight) ++ intWord g.threshold
def circuitWord {n : ℕ} (C : NCircuit n) : List Bool :=
  listWord gateWord C.gates ++ listWord intWord C.coeffs ++ listWord bitWord C.table
def ratWord (q : ℚ) : List Bool := intWord q.num ++ natWord q.den
def kindTag : CallKind → ℕ
  | .single => 0
  | .pair => 1
  | .parity => 2
def callWord (c : Call) : List Bool :=
  natWord c.n ++ natWord (kindTag c.kind) ++ circuitWord c.first ++ circuitWord c.second ++
    listWord natWord c.parity ++ ratWord c.radius
/-- The output `(p̂, κ̂)`. -/
def outputWord (o : ℚ × ℚ) : List Bool := ratWord o.1 ++ ratWord o.2

namespace Call

/-- The normalized calls at parameters `B₁, B₂`. -/
def Admitted (B1 B2 : ℕ) (c : Call) : Prop :=
  4 ≤ c.n ∧ c.first.WellFormed (B0 c.n) ∧ c.second.WellFormed (B0 c.n) ∧
    (c.kind ≠ .pair → c.second = NCircuit.empty c.n) ∧
    (c.kind ≠ .parity → c.parity = []) ∧ (∀ i ∈ c.parity, i < c.n) ∧
    c.W ≤ 2 * c.n ^ 4 ∧
    1 ≤ c.radius * (c.n : ℚ) ^ B1 ∧ c.radius ≤ 1 / 16 ∧ (ratWord c.radius).length ≤ c.n ^ B2 ∧
    c.parity.length ≤ c.n

end Call

/-- `𝒜₃(n) = n³ / (λ_n^{21/4} μ_n⁷)`. -/
noncomputable def A3 (n : ℕ) : ℝ :=
  (n : ℝ) ^ 3 / (((NearCubicGates.Target.lambda n : ℕ) : ℝ) ^ ((21 : ℝ) / 4) *
    ((NearCubicGates.Target.mu n : ℕ) : ℝ) ^ 7)

/-- `𝒜₁(n) = n^{7/2} / (λ_n⁶ μ_n⁸)`. -/
noncomputable def A1 (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((7 : ℝ) / 2) / (((NearCubicGates.Target.lambda n : ℕ) : ℝ) ^ 6 *
    ((NearCubicGates.Target.mu n : ℕ) : ℝ) ^ 8)

/-- A dyadic rational. -/
def IsDyadic (q : ℚ) : Prop := ∃ k : ℕ, (q * 2 ^ k).den = 1

/-- The counter of thm:pair-uniform at fixed `B₁, B₂`. -/
structure Counter (B1 B2 : ℕ) where
  /-- The interval `(p̂, κ̂)` the program prints on (call, witness word). -/
  value : Call → List Bool → ℚ × ℚ
  budget : Call → List Bool → ℕ
  /-- One ordinary program printing the interval, run on the call's word and the witness word. The worker
  only ever hands it call words, so nothing is asked on other words. -/
  program : WordFunction (Call × List Bool) (fun r => frame (callWord r.1) ++ frame r.2)
    (fun r => outputWord (value r.1 r.2)) (fun r => budget r.1 r.2)
  dyadic : ∀ c w, IsDyadic (value c w).1 ∧ IsDyadic (value c w).2
  sound : ∀ (c : Call) (w : List Bool), |(value c w).1 - c.prob| ≤ (value c w).2
  witnessLength : ℕ → ℕ
  witnessPoly : ∃ C k : ℕ, ∀ n, witnessLength n ≤ C * (n + 1) ^ k
  complete : ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 →
    (c.kind = .pair → (c.W : ℝ) ≤ a * (c.radius : ℝ) * A3 c.n) →
    (c.kind ≠ .pair → (c.W : ℝ) ≤ a * (c.radius : ℝ) * A1 c.n) →
    ∃ w : List Bool, w.length ≤ witnessLength c.n ∧ (value c w).2 ≤ c.radius
  fast : ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → c.Admitted B1 B2 → ∀ w : List Bool,
    budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n
  /-- Non-admitted calls are answered (with the default interval) in time polynomial in the call word, whatever the
  witness word: the worker relies on this instead of testing admission itself. -/
  rest : ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), ¬ c.Admitted B1 B2 →
    budget c w ≤ K * ((callWord c).length + 1) ^ e

end NearCubicGates.Close.Joins
