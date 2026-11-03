import Target
import NearCubicGates.FiniteAverages
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

namespace NearCubicGates.PublishedSources.Witness

open scoped BigOperators
open NearCubicWires FiniteAverages

/-- Every k-subset occurs once, and every assignment on its complement occurs
once. Uniform averaging over this finite type is the published restriction law. -/
abbrev FiniteRestriction (n k : ℕ) :=
  Σ I : {I : Finset (Fin n) // I.card = k}, {i : Fin n // i ∉ I.val} → Bool

/-- The full input lies in the cell specified by the outer assignment. -/
def cellAgrees {n k : ℕ} (ρ : FiniteRestriction n k) (x : BitInput n) : Prop :=
  ∀ (i : Fin n) (hi : i ∉ ρ.1.val), x i = ρ.2 ⟨i, hi⟩

/-- The gate is not constant on the cell. -/
def gateLive {n k : ℕ} (g : RealThresholdGate n) (ρ : FiniteRestriction n k) : Prop :=
  ∃ x z : BitInput n, cellAgrees ρ x ∧ cellAgrees ρ z ∧ g.eval x ≠ g.eval z

noncomputable def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

noncomputable def CTW26_AppendixA3_CentralBinomialRestriction : Prop := by
  classical
  exact ∀ (n k : ℕ), 0 < k → k < n → ∀ g : RealThresholdGate n,
    mean (fun ρ : FiniteRestriction n k => indicator (gateLive g ρ)) ≤
      ((k * Nat.choose (n - k) ((n - k) / 2) : ℕ) : ℝ) / (2 : ℝ) ^ (n - k)

/-- Mutual independence under uniform averaging, stated as joint-event
factorization for every finite subfamily (a hypothesis of the inequality).
For each i the range of Y i is finite. Any real event can be replaced by its
intersection with that finite range, a Borel set with the same preimage, so
this imposes no stronger notion of independence through measurability. -/
noncomputable def finiteIndependent {Samples Terms : Type*} [Fintype Samples]
    (Y : Terms → Samples → ℝ) : Prop := by
  classical
  exact ∀ (S : Finset Terms) (events : Terms → Set ℝ),
    mean (fun sample => indicator (∀ i ∈ S, Y i sample ∈ events i)) =
      ∏ i ∈ S, mean (fun sample => indicator (Y i sample ∈ events i))

/-- The finite uniform K = 1 specialization of the published bounded-variable
Bernstein inequality. The variance is the literal sum of second moments. -/
noncomputable def Vershynin18_Theorem2_8_4_FiniteBernstein : Prop := by
  classical
  exact ∀ (Samples Terms : Type*) [Fintype Samples] [Nonempty Samples]
      [Fintype Terms] [Nonempty Terms] (Y : Terms → Samples → ℝ),
    finiteIndependent Y →
    (∀ i, mean (Y i) = 0) →
    (∀ i sample, |Y i sample| ≤ 1) →
    ∀ s : ℝ, 0 < s →
      mean (fun sample => indicator (s ≤ |∑ i, Y i sample|)) ≤
        2 * Real.exp (-(s ^ 2) /
          (2 * ((∑ i, mean (fun sample => (Y i sample) ^ 2)) + s / 3)))

end NearCubicGates.PublishedSources.Witness
