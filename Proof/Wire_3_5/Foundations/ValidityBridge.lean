import Proof.Foundations.ComponentwiseValidity
import Proof.Wire_3_5.Foundations.MaskedExpectation

/-!
# S7 ↔ the Theorem 2.5 repository bridge, and B8's two finite-probability statements typed on the Theorem 2.5 repository's vocabulary  `clauseValue`, `validityPenalty` and `validityRound` are the Theorem 2.5 repository's
Realizes `tr:rounding` (P3:3512-3536) and `tr:sparse` (P3:3356-3387) in the vocabulary of the Theorem 2.5
`ComponentwiseValidity`; the paper quantities are the masked rounding loss and the sparse witness.
`ComponentwiseValidity` definitions: the masked transfer generalizes them, it does not re-define them.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires NearCubicWires.ComponentwiseValidity

theorem bitR_eq_bitAsReal (b : Bool) : bitR b = bitAsReal b := rfl

/-- The Theorem 2.5 repository's `booleanMean` is S7's `uMean` of the indicator (the §13.4 S7 gate: the Theorem 2.5 repository lemmas apply unchanged). -/
theorem booleanMean_eq_uMean {Ω : Type} [Fintype Ω] (b : Ω → Bool) :
    SupplierPipeline.booleanMean b = uMean (fun ω => bitR (b ω)) := rfl

/-- `tr:rounding` (P3:3512-3536) at the Theorem 2.5 repository's types.  Positions are `Clause × Fin 2`, so the uniform position
average is the incidence average of P3:3474-3475; masks may depend on the guess and the seed
(P3:3509-3511).  The hypotheses are the first two thresholds of `tr:thresholds` after the numerical
slack `ε₀ ≤ v₀` (P3:3486-3491).  `v₀ ≤ 1/24` replaces the paper's `v₀ ≤ 1/2` (Appendix D, finding F2). -/
def MaskedRounding : Prop :=
  ∀ {Clause Ω : Type} [Fintype Clause] [Fintype Ω]
    (S : Clause → Fin 2 → Ω → ℝ) (con : Clause → Fin 2 → Ω → Option Bool)
    (neg : Clause → Fin 2 → Bool) (G : Clause → Fin 2 → Ω → Bool) (v₀ : ℝ),
    0 < v₀ → v₀ ≤ 1 / 24 →
    uMean (fun p : Clause × Fin 2 × Ω =>
        bitR (G p.1 p.2.1 p.2.2) * validityPenalty (con p.1 p.2.1 p.2.2) (S p.1 p.2.1 p.2.2)) ≤ 3 * v₀ →
    uMean (fun p : Clause × Fin 2 × Ω => bitR (G p.1 p.2.1 p.2.2) * S p.1 p.2.1 p.2.2 ^ 2) ≤ 1 + 2 * v₀ →
    |uMean (fun p : Clause × Ω =>
        bitR (G p.1 0 p.2 && G p.1 1 p.2) *
          (clauseValue (neg p.1 0) (neg p.1 1) (S p.1 0 p.2) (S p.1 1 p.2) -
           clauseValue (neg p.1 0) (neg p.1 1)
             (bitAsReal (validityRound (con p.1 0 p.2) (S p.1 0 p.2)))
             (bitAsReal (validityRound (con p.1 1 p.2) (S p.1 1 p.2)))))| ≤
      5 * Real.sqrt (24 * v₀)

/-- `tr:sparse` (P3:3356-3387): the `L₄` sparse witness on the rational grid `Λ̄/s·{−1,0,1}`. -/
def SparseWitness : Prop :=
  ∀ {J Ω : Type} [Fintype J] [Fintype Ω] (C : J → Ω → Bool) (α : J → ℝ) (Λbar : ℝ) (s : ℕ),
    1 ≤ s → 1 ≤ Λbar → ∑ j, |α j| ≤ Λbar →
    ∃ (σ : Fin s → ℤ) (atom : Fin s → Option J), (∀ a, σ a ∈ ({-1, 0, 1} : Finset ℤ)) ∧
      uMean (fun x : Ω =>
        (Λbar / s * ∑ a, (σ a : ℝ) * (match atom a with | some j => bitR (C j x) | none => 0) -
          ∑ j, α j * bitR (C j x)) ^ 4) ≤ 19 * Λbar ^ 4 / (s : ℝ) ^ 2

end NearCubicWires.WireExponent3_5.Shared
