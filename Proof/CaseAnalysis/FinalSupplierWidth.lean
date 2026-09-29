import Proof.CaseAnalysis.FinalExactnessFamily
import Proof.CaseAnalysis.FinalSupplierAccuracy
import Proof.CaseAnalysis.FinalSupplierCalls
import Proof.CaseAnalysis.FinalThresholdWidths

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth

open NearCubicWires
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The external row count is a power of two

Paper A.8 (`paper.tex:2253-2255`) bounds "the logarithm of the number of
external rows".  For the production symmetric family that logarithm is an exact
natural number, because the rows ARE the walk seeds. -/

/-- The exponent of one canonical walk-seed space: `2 * sideBits` vertex bits
(`MargulisVertex m = ZMod m × ZMod m`) plus `160` bits per transition
(`card PoweredMargulisLabel = 16 ^ 40 = 2 ^ 160`), over the
`canonicalWalkLength denominator - 1 = 2 * Nat.clog 2 (denominator + 1)`
transitions of the canonical odd walk. -/
def walkExponent (sideBits denominator : ℕ) : ℕ :=
  2 * sideBits + 160 * (2 * Nat.clog 2 (denominator + 1))

/-- **The walk-seed space has exactly `2 ^ walkExponent` points.**  No estimate:
`card_positiveSample` splits the transcript, `card_poweredMargulisLabel` gives
the label alphabet, and `ZMod.card` gives the square vertex set. -/
theorem card_walkSample (sideBits denominator : ℕ) :
    Fintype.card (MargulisWalkSample (2 ^ sideBits) (canonicalWalkLength denominator))
      = 2 ^ walkExponent sideBits denominator := by
  have hlen : canonicalWalkLength denominator
      = (2 * Nat.clog 2 (denominator + 1)).succ := rfl
  rw [hlen, card_positiveSample, card_poweredMargulisLabel]
  have hvertex : Fintype.card (MargulisVertex (2 ^ sideBits))
      = 2 ^ sideBits * 2 ^ sideBits := by
    simp [MargulisVertex, Fintype.card_prod, ZMod.card]
  rw [hvertex, walkExponent]
  have h16 : (16 : ℕ) ^ 40 = 2 ^ 160 := by norm_num
  rw [h16, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
  ring_nf

/-- **The request's power-of-two exponent** — the paper's `h_D L_q` for the
production symmetric family, in closed form: the walk seed space built on the
graded Toeplitz rank of the request's occurrence pool, at the list denominator
the requested accuracy fixes. -/
def seedExponent (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale targetDenominator : ℕ) : ℕ :=
  walkExponent
    (toeplitzWalkSideBits
      (canonicalGradedRank (symmetricFourfoldOccurrences request).length
        (touchingCost (occurrenceSupport (symmetricFourfoldOccurrences request))
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale))))
    (symmetricListDenominator request targetDenominator)

/-- **`|\mathcal E| = 2 ^ seedExponent`** (paper A.13.9's `|\mathcal E|`, paper
A.8's external rows).  The production symmetric preprocessor's row count is a
power of two on the nose — which is what makes ONE uniform denominator possible
at all (§3). -/
theorem rowCount_eq_two_pow (spectrum : ExpanderSpectrumContract) (liveScale : ℕ)
    (target : ℕ → ℕ) (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (symmetricFourfoldRows spectrum liveScale target).rowCount request
      = 2 ^ seedExponent request liveScale (target request.q) :=
  card_walkSample _ _

/-! ## §2 `entryWidth` — one definition, two independent floors

`M.md` §11: neither floor dominates the other (counterexamples both ways), so
the definition is a `max` and both consumers come out of it by
`le_max_left` / `le_max_right`. -/

/-! ## §3 The answer channel — one uniform denominator

`realizes_of_stage` takes ONE `denominator : ℕ`.  A.13.9's own denominator
`|\mathcal E| * 2 ^ q = rowDenominator` is per-call, so the count is rescaled to
the uniform one. -/

/-- **The uniform denominator** `2 ^ (arity + scale)`.  A.13.9's `|\mathcal E|2^q`
with `|\mathcal E|` replaced by the common power of two `2 ^ scale`. -/
def denominator (arity scale : ℕ) : ℕ := 2 ^ (arity + scale)

/-- **The rescaled acceptance count**: A.13.9's `∑_e ∑_z T_{e,F(z)}(z)` carried
to the uniform denominator.  Where `rowDenominator ∣ denominator` this is exactly
`rowAnswer * (denominator / rowDenominator)`; elsewhere it is the floor, whose
error `answer_div_denominator_error` bounds by `1 / denominator`. -/
def answer {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity scale : ℕ)
    (factors : List (Circuit arity)) : ℕ :=
  rowAnswer rows arity factors * denominator arity scale
    / rowDenominator rows arity factors

/-- The acceptance count never exceeds the sample count: one `∑_e ∑_z` of bits
over `|\mathcal E| * 2 ^ q` samples. -/
theorem rowAnswer_le_rowDenominator {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (factors : List (Circuit arity)) :
    rowAnswer rows arity factors ≤ rowDenominator rows arity factors := by
  have hrow : ∀ index : Fin (rows.rowCount ⟨arity, factors⟩),
      (∑ input : BitInput arity,
        ((rows.aggregation ⟨arity, factors⟩).row index input).toNat)
        ≤ 2 ^ arity := by
    intro index
    calc (∑ input : BitInput arity,
            ((rows.aggregation ⟨arity, factors⟩).row index input).toNat)
        ≤ ∑ _input : BitInput arity, 1 :=
          Finset.sum_le_sum (fun input _ => by
            cases (rows.aggregation ⟨arity, factors⟩).row index input <;> simp)
      _ = 2 ^ arity := by simp
  calc rowAnswer rows arity factors
      = ∑ index : Fin (rows.rowCount ⟨arity, factors⟩),
          ∑ input : BitInput arity,
            ((rows.aggregation ⟨arity, factors⟩).row index input).toNat := rfl
    _ ≤ ∑ _index : Fin (rows.rowCount ⟨arity, factors⟩), 2 ^ arity :=
        Finset.sum_le_sum (fun index _ => hrow index)
    _ = rowDenominator rows arity factors := by
        simp [Finset.sum_const, rowDenominator]

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
