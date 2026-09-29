import Proof.Wire_3_5.Recovery.HybridLedger
import Proof.Wire_3_5.Assembly.Ok

/-! # The refuter's machine at `S₂` for a union leaf with the atom test

"the weak machine … rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid"
(P3:3669-3671). For a union leaf `U : UnionLeafAt2` (completeness at the accepting guesses WITH `AtomsOkG`):
`recMachine2Ok` (the union machine at `S₂` on the hierarchy language), `rejected_yes_eventually2Ok` (the refuter returns
a rejected yes-instance at every large length, P3:3675-3680), **`complete2Ok`** (the leaf's completeness at `S₂`).

Paper quantity of the main type: the union machine's acceptance at the accepting guesses passing the atom test. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RecoveryWitnessPolicy NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open Filter

section RefuterOk
variable (l : Literals) (G : Split.Gate) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
  (U : Split.UnionLeafAt2 (G.inputs kclk coef A a ha) (unionSetupS2 l G kclk coef A a ha))
  (P : FusedPrimitive (G.inputs kclk coef A a ha))

/-- The union machine at `S₂` on the hierarchy language. -/
noncomputable def recMachine2Ok : OrdinaryWeakMachine := U.build P (recL l kclk)

/-- **The refuter returns a rejected yes-instance of the machine at `S₂`** at every large length. -/
theorem rejected_yes_eventually2Ok :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      recL l kclk N ((recRefuter l kclk).output (recMachine2Ok l G U P) N) = true ∧
      ¬ (recMachine2Ok l G U P).accepts N ((recRefuter l kclk).output (recMachine2Ok l G U P) N) := by
  have hlittle := (U.toUnionConstruction.runtime3 P (recL l kclk)).littleO
  obtain ⟨n₀, hone⟩ := U.soundness P (recL l kclk) (recL_inNTIME l kclk)
  obtain ⟨onset, hsep⟩ := (recRefuter l kclk).eventual (recMachine2Ok l G U P) hlittle
  refine ⟨max onset n₀, fun N hN => ?_⟩
  have hiff := (hsep N (le_of_max_le_left hN)).2
  set x := (recRefuter l kclk).output (recMachine2Ok l G U P) N
  have hrej : ¬ (recMachine2Ok l G U P).accepts N x := fun hacc => by
    have h1 : recL l kclk N x = true := hone N (le_of_max_le_right hN) x hacc
    have h2 := hiff.1 hacc
    unfold recL at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  refine ⟨?_, hrej⟩
  unfold recL
  cases hx : (recRefuter l kclk).hierarchy.timedView.accepts N x
  · exact absurd (hiff.2 hx) hrej
  · rfl

/-- The union leaf's eventual completeness at `S₂`, at the hierarchy language, at the guesses passing the atom test. -/
theorem complete2Ok :
    ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess (recSetup2 l G kclk coef A a ha) z),
      UnionAccepts (recSetup2 l G kclk coef A a ha) P z g → AtomsOkG g → (recMachine2Ok l G U P).accepts N z := by
  have h := U.complete P (recL l kclk) (recL_inNTIME l kclk)
  rw [unionSetupS2_recL] at h
  exact h

end RefuterOk

end NearCubicWires.WireExponent3_5.Transfer
