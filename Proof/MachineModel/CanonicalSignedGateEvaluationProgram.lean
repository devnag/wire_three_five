import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalConditionalTouchProgram
import Proof.MachineModel.CanonicalIntPredecessorProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalStructuralGF2EvaluationProgram

open Finset
open scoped BigOperators

namespace NearCubicWires.CanonicalSignedGateEvaluationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalIntPredecessorProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalStructuralGF2EvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.ThresholdCompiler
open NearCubicWires.VerifiedLinker

/-! ## §1 Signed weights as two natural accumulators

A canonical integer weight splits into two naturals, exactly one of which is
nonzero.  Both halves are summed independently and compared at the very end,
so no intermediate register ever has to represent a negative number. -/

/-- The nonnegative half of a canonical integer weight. -/
def positivePart (value : ℤ) : ℕ := value.toNat

/-- The magnitude of the negative half of a canonical integer weight. -/
def negativePart (value : ℤ) : ℕ := (-value).toNat

theorem positivePart_sub_negativePart (value : ℤ) :
    (positivePart value : ℤ) - (negativePart value : ℤ) = value := by
  unfold positivePart negativePart
  omega

/-- The nonnegative half of a bit-selected weighted sum. -/
def maskedPositiveSum {n : ℕ} (weight : Fin n → ℤ) (bit : Fin n → Bool) : ℕ :=
  ∑ index, if bit index then positivePart (weight index) else 0

/-- The negative half of a bit-selected weighted sum. -/
def maskedNegativeSum {n : ℕ} (weight : Fin n → ℤ) (bit : Fin n → Bool) : ℕ :=
  ∑ index, if bit index then negativePart (weight index) else 0

theorem maskedScore_eq {n : ℕ} (weight : Fin n → ℤ) (bit : Fin n → Bool) :
    (∑ index, weight index * if bit index then (1 : ℤ) else 0) =
      (maskedPositiveSum weight bit : ℤ) -
        (maskedNegativeSum weight bit : ℤ) := by
  have hpositive :
      (maskedPositiveSum weight bit : ℤ) =
        ∑ index, if bit index then (positivePart (weight index) : ℤ) else 0 := by
    unfold maskedPositiveSum
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro index _
    cases bit index <;> simp
  have hnegative :
      (maskedNegativeSum weight bit : ℤ) =
        ∑ index, if bit index then (negativePart (weight index) : ℤ) else 0 := by
    unfold maskedNegativeSum
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro index _
    cases bit index <;> simp
  rw [hpositive, hnegative, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro index _
  cases bit index
  · simp
  · simpa using (positivePart_sub_negativePart (weight index)).symm

/-- **The signed gate comparison in naturals.**  Every later machine stage
compares these two natural totals and nothing else. -/
theorem gate_eval_eq_decide {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) :
    gate.eval input =
      decide
        (positivePart gate.threshold + maskedNegativeSum gate.weight input ≤
          maskedPositiveSum gate.weight input +
            negativePart gate.threshold) := by
  have hthreshold := positivePart_sub_negativePart gate.threshold
  have hscore := maskedScore_eq gate.weight input
  unfold NormalizedThresholdGate.eval
  rw [hscore]
  refine decide_eq_decide.mpr ?_
  omega

/-! ## §2 The score family in the same two accumulators

`liveScore`, `frozenScore`, and `minimumLiveScore` split the same weighted sum
along the live set.  Each is the difference of two `masked…Sum` values with a
different coordinate selector, so `residualConstant` lands on exactly the same
natural comparison as `NormalizedThresholdGate.eval`. -/

/-! ## §3 One coordinate's signed contribution, executed

The atom is the canonical integer syntax already stored in the typed
envelope, framed with the requested sign and the coordinate's bit:

```text
    Nat.pair (encodeInt w) (Nat.pair wanted bit)
```

Three fixed stages consume it.  A structural adapter puts the magnitude first
so the shared right-preserving wrapper can hand it to the canonical `encodeNat`
inverse; a final stage then selects the magnitude or zero using saturating
single-bit arithmetic only. -/

/-! ## §4 One signed accumulator over a whole atom list

A single balanced call of the per-atom stage followed by the existing balanced
natural sum produces one accumulator.  The atom list is a plain list of
`(weight, requested sign, bit)` triples: it is the only thing a later producer
has to assemble, and every sum below is an instance of it. -/

/-! Total projections of a raw request.  The balanced-call interface needs the
callee's fuel and output as functions of the request code alone. -/

/-! ## §5 The signed comparison machine

Two atom lists, one paired call of the accumulator, one saturating comparison.
Every quantity of Appendix A.2 is an instance of this single program; only the
two atom lists change. -/

/-! ## §6 Threshold-gate evaluation and the frozen-side residual bit

Both are the same comparison machine on two different atom lists.  The
threshold contributes one extra atom on each side — its own two nonnegative
parts — so no stage ever handles a negative register. -/

/-! ## §7 The two score halves, executed

`frozenScore` and `minimumLiveScore` are integers, so their executable content
is the pair of nonnegative halves the accumulator produces.  §2 already
identifies each score with those halves; the theorems below run them. -/

/-! ## §8 The residual variable

`residualVariable = eval xor residualConstant`.  Both bits come from the same
comparison machine under one paired call, so the whole residue is one fixed
oracle-free program over the gate's envelope syntax, the input mask, and the
abstract live mask. -/

/-! ## §9 The whole occurrence pool: the residual assignment table

The fourfold row table is `finiteAssignmentContext` of the pool's residual
assignment.  One balanced call of §8 over the pool, then the population is
paired back on.  The occurrence index rides inside each request so the map's
output is a projection of the request the balanced-call interface consumes;
the callee discards it in one instruction. -/

/-! ## §10 The fourfold row table

Pairing the population back onto the mapped bit list is exactly
`finiteAssignmentContext`, the row table the fourfold row evaluator consumes.
The request list and the population arrive together in one canonical pair. -/

end NearCubicWires.CanonicalSignedGateEvaluationProgram
