import Lean
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.Transfer.LiteralSources
import W3.Proof.Foundations.SourceRegistry
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Bindings.CLW20_Lemma3_10
import Bindings.CLW20_Lemma3_11_TM2
import Bindings.CLW20_Lemma3_8
import Bindings.CLW20_Lemma3_9_TM2
import Bindings.CLW20_Theorem1_13
import Bindings.CTW26_Lemma3_2
import Bindings.CW19_Proposition18_2_TM2
import Bindings.HLW06_Theorem8_2
import Bindings.RS62_Theorem4
import Bindings.TuringBridge.Budget
import Bindings.Williams14_Corollary4_4
import Proof.CaseAnalysis.FinalTapeLocality
import Statement
import Proof.Wire_3_5.UnionMachine.UnionSetupBase


noncomputable section


/-! # The pinned union setup with explicit constants `S₁` (P3:3485-3491, 3610-3614, 3685-3697; D1)

Realizes the union setup the recovery reads, with the masked verifier's constants chosen EXPLICITLY from the PCPP gap:
"First choose `β, ζ, δ` small relative to the fixed PCPP gap and `v₀`, and then choose `ξ` and the numerical error
small enough to leave slack in all three tests" (P3:3610-3614), and the oracle degree fixed before the machine:
"Before fixing this machine, choose `G` large enough that `G/c_STV` exceeds a general-Boolean simulation exponent for
both target classes and the desired polynomial advantage exponent, with a fixed positive margin" (P3:3685-3692).

`unionSetupS0` (M9) chose its constants by choice from `exists_unionParams`; the recovery needs the completeness
constants' `ζ` POSITIVE (the XOR lemma's accuracy `δ = ζ`, P3:3715-3724), which an opaque choice does not certify.
`unionSetupS1` is `S₀` with the explicit constants `unionSoundParams`/`unionCompleteParams` at a chosen rational
`ε ∈ (0, min(1, g/1000))` and threshold `τ` (`gateEps`, `gateTau`).

Paper quantities: `v₀, ε₀, τ` (`gateParams1`), `ζ, δ, β, ξ` (`gateCParams1`; `gateZeta_pos`, `gateZeta_lt`,
`gateDelta_pos`), `C_δ = ⌈5/δ²⌉` (`gateCδ1`, `gateCδ1_spec`), the oracle degree `G = 17·c_STV`
(`recOracleDeg`), and **`unionSetupS1 l G : G.Setup`** (the gate's pin, with `G` fixed). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

section Constants
variable (l : Literals)

theorem gap_pos : 0 < (gatePCPP l).completeness - (gatePCPP l).soundness := by
  have := (gatePCPP l).gap; linarith

theorem exists_eps : ∃ ε : ℚ, (0 : ℝ) < ε ∧
    (ε : ℝ) < min 1 (((gatePCPP l).completeness - (gatePCPP l).soundness) / 1000) :=
  exists_rat_btwn (by have := gap_pos l; positivity)

theorem exists_tau : ∃ τ : ℚ, ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 < τ ∧
    (τ : ℝ) < ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 +
      ((gatePCPP l).completeness - (gatePCPP l).soundness) / 10 :=
  exists_rat_btwn (by have := gap_pos l; linarith)

/-- The rational `ε` of the constants. -/
noncomputable def gateEps : ℚ := Classical.choose (exists_eps l)
/-- The rational threshold `τ`. -/
noncomputable def gateTau : ℚ := Classical.choose (exists_tau l)

theorem gateEps_pos : 0 < gateEps l := by
  have := (Classical.choose_spec (exists_eps l)).1
  unfold gateEps; exact_mod_cast this
theorem gateEps_le_one : gateEps l ≤ 1 := by
  have := lt_of_lt_of_le (Classical.choose_spec (exists_eps l)).2 (min_le_left _ _)
  unfold gateEps; exact_mod_cast this.le
theorem gateEps_le_gap : (gateEps l : ℝ) ≤ ((gatePCPP l).completeness - (gatePCPP l).soundness) / 1000 :=
  (lt_of_lt_of_le (Classical.choose_spec (exists_eps l)).2 (min_le_right _ _)).le
theorem gateTau_ge : ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 ≤ (gateTau l : ℝ) :=
  (Classical.choose_spec (exists_tau l)).1.le
theorem gateTau_le : (gateTau l : ℝ) ≤ ((gatePCPP l).completeness + (gatePCPP l).soundness) / 2 +
    ((gatePCPP l).completeness - (gatePCPP l).soundness) / 10 :=
  (Classical.choose_spec (exists_tau l)).2.le

/-- **The soundness constants**, explicit: `v₀ = ε²/10⁴`, `ε₀ = v₀/2`, outer error `ε/6`, threshold `τ`. -/
noncomputable def gateParams1 : MaskedSoundnessParameters (gatePCPP l).completeness (gatePCPP l).soundness :=
  unionSoundParams (gatePCPP l).soundnessPositive.le (gateEps l) (gateEps_pos l) (gateEps_le_one l)
    (gateEps_le_gap l) (gateTau l) (gateTau_ge l)

/-- **The completeness constants**, explicit: `ζ = (v₀/10)²`, `δ = v₀/100`, `β = ξ = ε/100`. -/
noncomputable def gateCParams1 : MaskedCompletenessParameters (gateParams1 l) :=
  unionCompleteParams (gatePCPP l).soundnessPositive.le (gateEps l) (gateEps_pos l) (gateEps_le_one l)
    (gateEps_le_gap l) (gateTau l) (gateTau_ge l) (gateTau_le l)

theorem gateZeta_eq : (gateCParams1 l).ζ = ((gateEps l ^ 2 / 10000) / 10) ^ 2 := rfl
theorem gateDelta_eq : (gateCParams1 l).δ = (gateEps l ^ 2 / 10000) / 100 := rfl
theorem gateBeta_eq : (gateCParams1 l).β = gateEps l / 100 := rfl

theorem gateZeta_pos : 0 < (gateCParams1 l).ζ := by
  rw [gateZeta_eq]; have := gateEps_pos l; positivity

theorem gateZeta_lt : (gateCParams1 l).ζ < 1 / 2 := by
  rw [gateZeta_eq]
  have h0 := gateEps_pos l
  have h1 := gateEps_le_one l
  have h2 : gateEps l ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  have h3 : (gateEps l ^ 2 / 10000 / 10) ≤ 1 / 100000 := by
    have : gateEps l ^ 2 / 10000 / 10 = gateEps l ^ 2 / 100000 := by ring
    rw [this]; exact div_le_div_of_nonneg_right h2 (by norm_num)
  have h4 : 0 ≤ gateEps l ^ 2 / 10000 / 10 := by positivity
  nlinarith

theorem gateDelta_pos : 0 < (gateCParams1 l).δ := by
  rw [gateDelta_eq]; have := gateEps_pos l; positivity

/-- `C_δ = ⌈5/δ²⌉` at the explicit `δ`. -/
noncomputable def gateCδ1 : ℕ := ⌈(5 : ℚ) / (gateCParams1 l).δ ^ 2⌉₊

theorem gateCδ1_spec : 5 ≤ ((gateCδ1 l : ℕ) : ℚ) * (gateCParams1 l).δ ^ 2 := by
  have hpos : 0 < (gateCParams1 l).δ ^ 2 := by have := gateDelta_pos l; positivity
  have hc : (5 : ℚ) / (gateCParams1 l).δ ^ 2 ≤ (gateCδ1 l : ℚ) := Nat.le_ceil _
  calc (5 : ℚ) = 5 / (gateCParams1 l).δ ^ 2 * (gateCParams1 l).δ ^ 2 := (div_mul_cancel₀ 5 hpos.ne').symm
    _ ≤ (gateCδ1 l : ℚ) * (gateCParams1 l).δ ^ 2 := by gcongr

theorem gateCδ1_pos : 1 ≤ gateCδ1 l := by
  have h := gateCδ1_spec l
  rcases Nat.eq_zero_or_pos (gateCδ1 l) with h0 | h0
  · rw [h0] at h; norm_num at h
  · exact h0

/-- **The oracle degree** `G = 17·c_STV` (Case 1's simulation margin, P3:3685-3692). -/
noncomputable def recOracleDeg : ℕ := 17 * l.eightSources.amplification.stvExponent

end Constants

variable (l : Literals) (G : Split.Gate)

/-- The masked verifier's outer error `ε/6` is positive (the reserve of Lemma H.3's proof is then met past an onset). -/
theorem gateOuterError_pos : (0 : ℝ) < ((gateParams1 l).outerError : ℝ) := by
  have h : (gateParams1 l).outerError = gateEps l / 6 := rfl
  rw [h]
  have := gateEps_pos l
  exact_mod_cast (show (0 : ℚ) < gateEps l / 6 by positivity)

/-- **The setup off the recovered language** (`S₁`): the hierarchy `choose (L ∈ NTIME(T))`, its succinct verifier at
`λ_a`, the explicit constants, the oracle degree `17·c_STV`, and `live = false`: the machine rejects outright there, so
soundness and time hold trivially and completeness is vacuous. -/
noncomputable def unionSetupS1 : G.Setup := fun kclk coef A a ha L hL =>
  setupOf (G.inputs kclk coef A a ha) L (hierarchyOf hL) (Classical.choose_spec hL) (gateMW l) (lenG l)
    (Classical.choice (NearCubicGates.Close.Succinct.succinctVerifier_exists (hierarchyOf hL) (lenG l))) (gatePCPP l)
    false (recOracleDeg l) (gateParams1 l) (gateOuterError_pos l) (gridMassOf (gateCδ1 l) G.row.sp)
    (fun _ => by unfold gridMassOf; positivity) G.row.sp

theorem unionSetupS1_live (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) : (unionSetupS1 l G kclk coef A a ha L hL).live = false := rfl

end NearCubicWires.WireExponent3_5.Transfer

end
