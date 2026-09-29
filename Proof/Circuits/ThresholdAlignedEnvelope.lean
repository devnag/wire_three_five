import Proof.Foundations.SupplierPrime

open Finset
open scoped BigOperators

namespace NearCubicWires.ThresholdAlignedEnvelope

open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime

/-! ## §1 The two generic folds -/

/-- Natural-number Horner fold: `[a₀, a₁, …] ↦ a₀ + base * (a₁ + base * …)`.
Mirrors the shape of `stackEquations` on the magnitude side. -/
def natHornerFold (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | head :: tail => head + base * natHornerFold base tail

/-! ## §2 The stack-magnitude Horner bound (the file's one real lemma) -/

/-- The magnitude of a mixed-radix stack is dominated by the Horner fold of
the per-equation magnitudes at the base's absolute value.  Pure triangle
inequalities — no sign or block condition is needed for the `≤` direction. -/
theorem equationMagnitudeBound_stackEquations_le
    {Carrier : Type} [Fintype Carrier] (base : ℤ)
    (equations : List (LabelledEquation Carrier)) :
    equationMagnitudeBound (stackEquations base equations) ≤
      natHornerFold base.natAbs (equations.map equationMagnitudeBound) := by
  induction equations with
  | nil =>
      simp [stackEquations, equationMagnitudeBound, natHornerFold]
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, natHornerFold]
      have hweights : ∀ index : Carrier,
          (head.weights index +
              base * (stackEquations base tail).weights index).natAbs ≤
            (head.weights index).natAbs +
              base.natAbs *
                ((stackEquations base tail).weights index).natAbs := by
        intro index
        calc (head.weights index +
                base * (stackEquations base tail).weights index).natAbs ≤
              (head.weights index).natAbs +
                (base * (stackEquations base tail).weights index).natAbs :=
            Int.natAbs_add_le _ _
          _ = (head.weights index).natAbs +
                base.natAbs *
                  ((stackEquations base tail).weights index).natAbs := by
            rw [Int.natAbs_mul]
      have htarget :
          (head.target + base * (stackEquations base tail).target).natAbs ≤
            head.target.natAbs +
              base.natAbs * (stackEquations base tail).target.natAbs := by
        calc (head.target + base * (stackEquations base tail).target).natAbs ≤
              head.target.natAbs +
                (base * (stackEquations base tail).target).natAbs :=
            Int.natAbs_add_le _ _
          _ = head.target.natAbs +
                base.natAbs * (stackEquations base tail).target.natAbs := by
            rw [Int.natAbs_mul]
      have hsum :
          (∑ index, (head.weights index +
              base * (stackEquations base tail).weights index).natAbs) ≤
            (∑ index, (head.weights index).natAbs) +
              base.natAbs * ∑ index,
                ((stackEquations base tail).weights index).natAbs := by
        calc (∑ index, (head.weights index +
                base * (stackEquations base tail).weights index).natAbs) ≤
              ∑ index, ((head.weights index).natAbs +
                base.natAbs *
                  ((stackEquations base tail).weights index).natAbs) :=
            Finset.sum_le_sum fun index _ => hweights index
          _ = (∑ index, (head.weights index).natAbs) +
                base.natAbs * ∑ index,
                  ((stackEquations base tail).weights index).natAbs := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      change (∑ index, (head.weights index +
            base * (stackEquations base tail).weights index).natAbs) +
          (head.target + base * (stackEquations base tail).target).natAbs ≤
        equationMagnitudeBound head +
          base.natAbs *
            natHornerFold base.natAbs (tail.map equationMagnitudeBound)
      calc (∑ index, (head.weights index +
              base * (stackEquations base tail).weights index).natAbs) +
            (head.target + base * (stackEquations base tail).target).natAbs ≤
            ((∑ index, (head.weights index).natAbs) +
              base.natAbs * ∑ index,
                ((stackEquations base tail).weights index).natAbs) +
            (head.target.natAbs +
              base.natAbs * (stackEquations base tail).target.natAbs) :=
          Nat.add_le_add hsum htarget
        _ = equationMagnitudeBound head +
              base.natAbs *
                equationMagnitudeBound (stackEquations base tail) := by
          unfold equationMagnitudeBound
          ring
        _ ≤ equationMagnitudeBound head +
              base.natAbs *
                natHornerFold base.natAbs (tail.map equationMagnitudeBound) := by
          gcongr

/-! ## §3 The aligned threshold envelope -/

/-- Magnitude of one raw child gate: total weight mass plus target mass.
Under the segment embedding this equals the embedded child equation's
`equationMagnitudeBound` (bridge proved beside `thresholdChildEquation`). -/
def childMagnitude {arity : ℕ} (gate : ExactThresholdGate arity) : ℕ :=
  (∑ index, (gate.weight index).natAbs) + gate.target.natAbs

end NearCubicWires.ThresholdAlignedEnvelope
