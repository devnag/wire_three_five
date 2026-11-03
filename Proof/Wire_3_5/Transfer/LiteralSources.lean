import Lean
import Statement_Wire_3_5
import W3.Proof.Foundations.SourceRegistry
import Proof.Wire_3_5.Foundations.Sources35
import Bindings.CLW20_Lemma3_9
import Proof.Foundations.PolynomialClock
import Proof.Foundations.RecoveryScheduleEnvelope
import Outer.Source
import Bindings.CTW26_Lemma3_2
import Bindings.CW19_Proposition18_2_TM2
import Bindings.Williams14_Corollary4_4
import Bindings.HLW06_Theorem8_2
import Bindings.RS62_Theorem4
import Bindings.CLW20_Lemma3_11_TM2
import Bindings.CLW20_Theorem1_13
import Bindings.CLW20_Lemma3_8
import Bindings.CLW20_Lemma3_9_TM2


/-! # The literals supply the source bundle

Realizes the use of the imported results (paper §H.1, `tr:imports`) through the source bundle `Sources35`, at the range
the proof reads. Its short-PCP field is the Murray–Williams source `MWSource` (§H.1, item 1: "We apply this interface
once, to the fixed verifier 𝒱_G of Lemma H.6"), from the sixth literal `mw20` by `mwSource_of_literal`; the refuter at
the clocks `n^(k+2)` comes from the eighth literal (`at_to_algorithm`), the amplifier at the degree `17·⌈c⌉` from the
ninth (`amplifier35`: `S = oracleSizeBound (17⌈c⌉)` grows at least like `n^c`); the other fields come from the
remaining literals by the Theorem 2.5 adapters, with the XOR source proved in Lean (`CLW20Lemma38.clw20_xor_source`).
The paper quantity of the main type is the bundle `Sources35`. -/

set_option autoImplicit false


namespace NearCubicWires.WireExponent3_5
open _root_.NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-- `S(n) = oracleSizeBound d n` grows at least like `n^c` once `⌈c⌉ ≤ d`. -/
theorem rpow_le_oracleSizeBound (c : ℝ) (hc : 1 ≤ c) (d : ℕ) (hd : ⌈c⌉₊ ≤ d) (n : ℕ) :
    (n : ℝ) ^ c ≤ (oracleSizeBound d n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
    exact Nat.cast_nonneg _
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (n : ℝ) ^ c ≤ (n : ℝ) ^ ((⌈c⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil c)
    rw [Real.rpow_natCast] at h1
    have h2 : n ^ ⌈c⌉₊ ≤ oracleSizeBound d n := by
      have hdep := _root_.NearCubicWires.RecoveryScheduleEnvelope.requiredDegree_le_oracleDegree d
      calc n ^ ⌈c⌉₊ ≤ n ^ (2 ^ _root_.NearCubicWires.RecoveryScheduleEnvelope.oracleDepth d) :=
            Nat.pow_le_pow_right hn (hd.trans hdep)
        _ ≤ _root_.NearCubicWires.PolynomialClock.pairClock
              (_root_.NearCubicWires.RecoveryScheduleEnvelope.oracleDepth d) n :=
            _root_.NearCubicWires.PolynomialClock.pow_twoPow_le_pairClock _ n
    calc (n : ℝ) ^ c ≤ (n : ℝ) ^ ⌈c⌉₊ := h1
      _ = ((n ^ ⌈c⌉₊ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (oracleSizeBound d n : ℝ) := by exact_mod_cast h2

/-- The ninth literal gives the amplifier at the degree `17·⌈c⌉`. -/
theorem amplifier35 (h : CLW20_Lemma3_9_TM2_Large) :
    Nonempty NearCubicWires.RepairSource.AmplifierAt35 := by
  obtain ⟨c, hc, hS⟩ := h
  obtain ⟨W⟩ := hS (oracleSizeBound (17 * ⌈c⌉₊))
    (_root_.NearCubicWires.RecoveryScheduleEnvelope.oracleSizeBoundConstructible _)
    (rpow_le_oracleSizeBound c hc _ (by omega))
  exact ⟨{ stvExponent := ⌈c⌉₊
           stvExponentPositive := Nat.ceil_pos.mpr (by linarith)
           schedule := _root_.NearCubicWires.Bindings.CLW20Lemma39.scheduleAmplifierOfLiteral hc _ W.toTier1 }⟩

/-- The nine literals give the source bundle `Sources35` (short PCP from `mw20`, §H.1 item 1; refuter at `n^(k+2)`;
amplifier at `17·⌈c⌉`). -/
theorem Literals.eightSources (lit : Literals) : NearCubicWires.RepairSource.Sources35 where
  normalization := _root_.NearCubicWires.Bindings.CTW26.ctw26_to_import lit.ctw26
  decomposition := _root_.NearCubicWires.Bindings.CW19TM2.cw19_tm2_to_import lit.cw19
  williams := _root_.NearCubicWires.Bindings.Williams14.williams14_to_import lit.williams
  expander := _root_.NearCubicWires.Bindings.HLW06.hlw06_to_import lit.hlw06
  prime := _root_.NearCubicWires.Bindings.RS62.rs62_to_import lit.rs62
  pcp := ⟨_root_.NearCubicGates.Close.Outer.mwSource_of_literal lit.mw20,
    _root_.NearCubicWires.Bindings.CLW20Lemma311TM2.clw20_lemma3_11_explicitEnc_tm2_to_import lit.clw311⟩
  refuter := fun k => _root_.NearCubicWires.Bindings.CLW20Theorem113.at_to_algorithm (lit.clw113 k)
  xor := _root_.NearCubicWires.Bindings.CLW20Lemma38.clw20_xor_source
  amplifier := amplifier35 lit.clw39

end NearCubicWires.WireExponent3_5

