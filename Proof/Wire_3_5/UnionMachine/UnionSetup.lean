import Lean
import Proof.Wire_3_5.UnionMachine.UnionAtoms
import Proof.Wire_3_5.UnionMachine.UnionParams
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Assembly.Split
import Proof.Hierarchy.CompetitorSourceAverage
import Proof.Foundations.ProjectionPCPPadding
import Statement_Wire_3_5
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionSetupBase


noncomputable section


/-! # The union setup from the outer data (Lemma H.7; order of the constants)

Realizes the data the union machine fixes before it is presented to the refuter, in the order of the constants: the
hierarchy deciding the language at the clock `N^{kclk+2}`, the short PCP (§H.1 item 1), the succinct verifier `𝒱_G` of
Lemma H.6 at the description length `λ_a`, the pointwise PCPP (§H.1 item 2), the oracle exponent, the masked verifier's
constants, and the grid; the length gate's onset comes last (Lemma H.3's proof: "For all sufficiently large N,
s_out(N)=1/λ_a ≤ (c_p−s_p)/8").

Paper quantities: **`exists_onset`** (past it: `𝒱_G`'s onset, `q(N)` at least the PCPP's minimum arity, `1/λ_a ≤ η`),
**`setupOf`** (`UnionSetup` from the outer data), the masked verifier's constants `gateParams`, `gateCParams`, and the
grid ratio `gateCδ`. The outer soundness `1/λ_a` itself is `UnionSetup.outerSound` (Lemma H.7(c)). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

/-! ## A setup from the outer data -/

section Setup
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **The length gate's onset exists** (Lemma H.3's proof: "For all sufficiently large N, s_out(N)=1/λ_a ≤ …"; the
order of the constants puts it after `𝒱_G` and the PCPP): past it, `𝒱_G` is past its own onset, `q(N)` reaches the
PCPP's minimum arity, and `1/λ_a ≤ η`. -/
theorem exists_onset (mw : NearCubicGates.Close.Outer.MWSource) {H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))}
    {lenG : ℕ} (SV : NearCubicGates.Close.Outer.SuccinctVerifier H lenG) (a : PointwisePCPPAlgorithm) (η : ℝ)
    (hη : 0 < η) :
    ∃ onset : ℕ, SV.onset ≤ onset ∧ 1 ≤ onset ∧
      (∀ ν, onset ≤ ν → a.minimumArity ≤ NearCubicGates.Close.Outer.width mw SV (2 ^ ν)) ∧
      (∀ ν, onset ≤ ν → 1 / (NearCubicGates.Close.Outer.instLength lenG ν : ℝ) ≤ η) := by
  refine ⟨SV.onset + 1 + a.minimumArity + ⌈1 / η⌉₊, by omega, by omega, fun ν hν => ?_, fun ν hν => ?_⟩
  · have := W3.NearCubicWires.RepairSource.Outer3.nu_lt_width mw SV ν
    omega
  · have hν1 : 1 ≤ ν := by omega
    have hpow : ν ≤ NearCubicGates.Close.Outer.instLength lenG ν := by
      unfold NearCubicGates.Close.Outer.instLength
      calc ν = ν ^ 1 := (pow_one ν).symm
        _ ≤ ν ^ (lenG + 2) := Nat.pow_le_pow_right hν1 (by omega)
    have hK : (1 / η : ℝ) ≤ (NearCubicGates.Close.Outer.instLength lenG ν : ℝ) := by
      have h1 : (1 / η : ℝ) ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈1 / η⌉₊ : ℝ) ≤ (ν : ℝ) := by exact_mod_cast (show ⌈1 / η⌉₊ ≤ ν by omega)
      have h3 : (ν : ℝ) ≤ (NearCubicGates.Close.Outer.instLength lenG ν : ℝ) := by exact_mod_cast hpow
      linarith
    have hpos : (0 : ℝ) < (NearCubicGates.Close.Outer.instLength lenG ν : ℝ) := by
      have : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν1
      have h3 : (ν : ℝ) ≤ (NearCubicGates.Close.Outer.instLength lenG ν : ℝ) := by exact_mod_cast hpow
      linarith
    rw [div_le_iff₀ hpos]
    rw [div_le_iff₀ hη] at hK
    linarith

/-- **The union setup from the outer data** (Lemma H.7; order of the constants): a hierarchy `H` deciding `L`, the
short PCP, the succinct verifier `𝒱_G` at `λ_a = instLength lenG a`, the pointwise PCPP, the liveness flag, the oracle
exponent, the masked verifier's constants (with a positive outer error) and the grid; the onset is `exists_onset`'s. -/
noncomputable def setupOf (I : PrimitiveInputs B) (L : Language) (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2)))
    (hL : ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x)
    (mw : NearCubicGates.Close.Outer.MWSource) (lenG : ℕ) (SV : NearCubicGates.Close.Outer.SuccinctVerifier H lenG)
    (a : PointwisePCPPAlgorithm) (live : Bool) (G : ℕ) (params : MaskedSoundnessParameters a.completeness a.soundness)
    (hη : 0 < (params.outerError : ℝ)) (gridMass : ℕ → ℚ) (hmass : ∀ q, 0 ≤ gridMass q) (gridSize : ℕ → ℕ) :
    UnionSetup I where
  language := L
  hier := H
  decides := hL
  mw := mw
  lenG := lenG
  SV := SV
  pcppAlg := a
  live := live
  G := G
  params := params
  onset := Classical.choose (exists_onset mw SV a _ hη)
  onset_sv := (Classical.choose_spec (exists_onset mw SV a _ hη)).1
  onset_pos := (Classical.choose_spec (exists_onset mw SV a _ hη)).2.1
  onset_arity := (Classical.choose_spec (exists_onset mw SV a _ hη)).2.2.1
  onset_reserve := (Classical.choose_spec (exists_onset mw SV a _ hη)).2.2.2
  gridMass := gridMass
  gridMass_nonneg := hmass
  gridSize := gridSize
  constAtom := unionConstAtom
  constAtom_eval := unionConstAtom_eval
  constAtom_gates := unionConstAtom_gates
  parityAtom := unionParityAtom
  parityAtom_eval := unionParityAtom_eval

end Setup

/-! ## The gate's setup `S₀` -/

end NearCubicWires.WireExponent3_5.Transfer

end
