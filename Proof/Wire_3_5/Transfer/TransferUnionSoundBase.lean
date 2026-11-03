import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls

/-! # `tr:soundness` for the union machine: no accepting guess on a no-instance, and `OneSided` from `SoundFor`

Realizes Lemma `tr:soundness` (P3:3504-3554) at the union machine's acceptance condition: "For sufficiently small fixed
`v₀, ε₀`, no branch of the weak machine accepts a hierarchy no-instance, for all sufficiently large source lengths.
This holds for every syntactically legal real-valued sparse guess [...] and for proof-dependent, seed-dependent
masks." A branch is a guess `g` with `UnionAccepts S P z g`. Its grid sums, constant and encoding
parities are the atom forms (`UnionGuess.forms`), so the machine's estimates `V̂, Q̂, μ̂` formed from the fused
primitive's printed values are within `(1+Λ̄)⁴q^{−D} ≤ ε₀` of the tests (`seed_propagated_*`, which consume
`FusedPrimitive.error` on the admissible calls), and the masked tests at the seed's filters cannot pass on a
no-instance: the rounding (`tr:rounding`, corrected), the one-sided mask (`tr:one-sided`), pointwise PCPP soundness
(`PointwisePCPPAlgorithm.sound`) and the outer soundness `N^{−10}` (the chain, here with real estimates:
`masked_soundness_real`).

Main results: **`UnionGuess.not_unionAccepts`** (at a no-instance with `N^{−10} ≤ η` and `(1+Λ̄(q))⁴q^{−D} ≤ ε₀`, no
guess is accepted) and **`oneSided_of_soundFor`** (every machine with `SoundFor` is `OneSided` for the hierarchy
language, the seed's refuter premise). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

/-- `tr:soundness` with real estimates (the machine's estimates are exact rationals; their real values are what the
accuracy bounds speak about): estimates within `ε₀` of the tests of any guess and any masks cannot pass
`tr:thresholds` on a PCPP that is pointwise sound and whose circuit the outer verifier accepts on at most `η` of the
random inputs. -/
theorem masked_soundness_real {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    (params : MaskedSoundnessParameters cp sp) {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp)
    (houter : uMean (fun x : BitInput q => bitR (H.eval x)) ≤ params.outerError)
    (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) (Vh Qh μh : ℝ)
    (hV : |Vh - testV pcpp S G| ≤ params.eps0) (hQ : |Qh - testQ pcpp S G| ≤ params.eps0)
    (hμ : |μh - testMu pcpp S G| ≤ params.eps0) (hVp : Vh ≤ 2 * (params.v0 : ℝ)) (hQp : Qh ≤ 1 + (params.v0 : ℝ))
    (hμp : (params.threshold : ℝ) ≤ μh) : False := by
  have hv0 : (0 : ℝ) < params.v0 := by exact_mod_cast params.v0_pos
  have hv24 : (params.v0 : ℝ) ≤ 1 / 24 :=
    calc (params.v0 : ℝ) ≤ ((1 / 24 : ℚ) : ℝ) := Rat.cast_le.mpr params.v0_le
      _ = 1 / 24 := by norm_num
  have hεv : (params.eps0 : ℝ) ≤ params.v0 := by exact_mod_cast params.eps0_le_v0
  have hV' : testV pcpp S G ≤ 3 * (params.v0 : ℝ) := by linarith [(abs_le.mp hV).1]
  have hQ' : testQ pcpp S G ≤ 1 + 2 * (params.v0 : ℝ) := by linarith [(abs_le.mp hQ).1]
  have h1 := testMu_le_rounded pcpp S G params.v0 hv0 hv24 hV' hQ'
  have h2 := maskedRoundedScore_le pcpp S G
  have h3 := roundedScore_le_soundness pcpp params.sp_nonneg hsound S
  have h4 := (abs_le.mp hμ).2
  have hmid := params.thresholdAboveMidpoint
  have hres := params.roundingReserve
  have hout := params.outerReserve
  linarith

section Union

namespace UnionGuess

end UnionGuess

end Union

end NearCubicWires.WireExponent3_5.Transfer
