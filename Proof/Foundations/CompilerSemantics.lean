import Proof.Foundations.Semantics
import Proof.Foundations.ThresholdCompiler

/-!
# Semantic adapter for the executable threshold compiler

`ThresholdCompiler` proves the corrected crossing algorithm over integer
equations.  This module is the only adapter from that executable representation
to the exact-gate representation used by the source interfaces and headlines.
-/

namespace NearCubicWires.CompilerSemantics

open NearCubicWires.ThresholdCompiler

/-- Integer non-strict syntax `[score ≥ θ]` is the strict gate
`[score > θ - 1]`; no coefficient or support changes. -/
def nonStrictAsStrict {n : ℕ} (gate : NormalizedThresholdGate n) :
    NormalizedThresholdGate n where
  weight := gate.weight
  threshold := gate.threshold - 1

theorem nonStrictAsStrict_eval {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) :
    (nonStrictAsStrict gate).strictEval input = gate.eval input := by
  simp only [NormalizedThresholdGate.strictEval, NormalizedThresholdGate.eval,
    nonStrictAsStrict]
  apply decide_eq_decide.mpr
  omega

theorem normalizedScore_eq_bitInt {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) :
    (∑ i, gate.weight i * if input i then 1 else 0) =
      ∑ i, gate.weight i * bitInt (input i) := by
  apply Finset.sum_congr rfl
  intro index _
  cases input index <;> rfl

end NearCubicWires.CompilerSemantics
