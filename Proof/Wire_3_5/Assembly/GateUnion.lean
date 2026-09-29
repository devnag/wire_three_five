import Bindings.CLW20_Lemma3_10_TM2
import Bindings.CLW20_Lemma3_10_Wrapper
import Bindings.CLW20_Lemma3_11_TM2
import Proof.Hierarchy.HierarchyNormalizedRealization
import Proof.PCP.PCPPNativeHierarchyEnvelope
import Proof.Wire_3_5.Foundations.Skeleton
import Proof.Wire_3_5.Ledger.LedgerWidth

/-! # The union's gate constants from the literals (P3:3637-3655, 3797-3798)

Realizes, as definitions from the literal constants, the numbers the reads from the union:
"pad the outer verifier to the exact width `q(N) = ⌈log₂T(N)⌉ + A_pad⌈log₂(log₂T(N)+2)⌉ + A_pad`, where `A_pad` exceeds
the imported polylogarithmic proof-length exponent" (P3:3637-3641); "The source preprocessing costs
`N^{d_ver}q^{O_G(1)}` for a fixed source exponent `d_ver`; choose `C_clk > d_ver + 2`" (P3:3653-3655); "polynomially many
verification calls" (P3:3797-3798).

Paper quantities:
* `gateSource l`: the one projection-PCP source (CLW20 Lemma 3.10, literal `clw310`) applied to base's fixed universal
  verifier `UWhole` (`UWhole.projectionSource`), fixed before the hierarchy exponent;
* `gatePCPP l`: the pointwise PCPP (CLW20 Lemma 3.11, literal `clw311`);
* `gateApad l = p₀ + 6`, `p₀` the source's proof-length exponent: the normalized PCP proves
  `2^{R(n)} ≤ C·time(n)·logScale(time n)^{5+p₀}` (base `HierarchyEncodeReady.normalizedRun`), and
  **`width_le_nativeWidth`** shows that any width with such a bound lies below `q(N)` at `A_pad = p + 1` eventually;
* `gateDver l`: base's source-work exponent of the whole hierarchy/oracle/PCPP pipeline
  (`PCPPNativeHierarchySource.inputExponent`, the exponent of `CaseTwoWholeBudgetHierarchy.envelope`): the union leaf
  takes `C_clk = kclk + 2` with `kclk ≥ d_ver` and source work `(N+1)^{d_ver+1}`;
* `gateCallDeg l G = 5·σ_H·d_a + 1`, `σ_H = max(e_Q + 2^{oracleDepth G}, 3e_Q)`: the exponent of the call count
  `24K(1+2K(s+1))⁴` (`length_schedule_le`) for the substituted circuit of size `O(q^{σ_H})` at oracle degree `G`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary

/-- The projection-PCP source at base's universal verifier, from the `clw310` literal. -/
noncomputable def gateSource (l : Literals) : ProjectionSourceAlgorithm UWhole.verifier UWhole.time :=
  UWhole.projectionSource
    (Bindings.CLW20Lemma310Guard.clw20_lemma3_10_to_import (Bindings.CLW20Lemma310TM2.tier1_of_tier2 l.clw310))

/-- The pointwise PCPP algorithm, from the `clw311` literal. -/
noncomputable def gatePCPP (l : Literals) : PointwisePCPPAlgorithm :=
  Classical.choice (Bindings.CLW20Lemma311TM2.clw20_lemma3_11_explicitEnc_tm2_to_import l.clw311)

/-- **`A_pad`** `= p₀ + 6`: one more than the normalized PCP's proof-length exponent `5 + p₀`. -/
noncomputable def gateApad (l : Literals) : ℕ := (gateSource l).degrees.proofLog + 6

/-- **`d_ver`**: the source-work exponent of the hierarchy/oracle/PCPP pipeline. -/
noncomputable def gateDver (l : Literals) : ℕ :=
  PCPPNativeHierarchySource.inputExponent (gateSource l) (gatePCPP l)

/-- The size exponent of the substituted circuit at oracle degree `G`: queries `(q+1)^{e_Q}` times an oracle of size
`(q+1)^{2^{oracleDepth G}}`, and the compacted `3CNF` on the query answers. -/
def unionSigmaH (eQ oracleDeg : ℕ) : ℕ := max (eQ + 2 ^ RecoveryScheduleEnvelope.oracleDepth oracleDeg) (3 * eQ)

/-- **`callDeg`** at oracle degree `G`. -/
noncomputable def gateCallDeg (l : Literals) (oracleDeg : ℕ) : ℕ :=
  5 * unionSigmaH (gateSource l).degrees.queries oracleDeg * (gatePCPP l).degree + 1

/-! ## The forcing inequality of `A_pad` -/

theorem clog_add_le (c T : ℕ) (hT : 1 ≤ T) :
    Nat.clog 2 (c * (T + 1) + 2) ≤ Nat.clog 2 T + (Nat.clog 2 (c + 2) + 2) := by
  rw [Nat.clog_le_iff_le_pow (by norm_num), pow_add]
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) T
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 2) (c + 2)
  have h3 : c * (T + 1) + 2 ≤ (c + 2) * (2 * T) := by nlinarith
  calc c * (T + 1) + 2 ≤ (c + 2) * (2 * T) := h3
    _ ≤ 2 ^ Nat.clog 2 (c + 2) * (2 * 2 ^ Nat.clog 2 T) := Nat.mul_le_mul h2 (by omega)
    _ ≤ 2 ^ Nat.clog 2 T * 2 ^ (Nat.clog 2 (c + 2) + 2) := by rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := Nat.clog 2 T)]

/-- **The padded width dominates the PCP's width** eventually: if `2^{R(n)} ≤ C·c(n^{k+2}+1)·logScale(c(n^{k+2}+1))^p`
(the normalized PCP's `proofBound`, with `time n = c(n^{k+2}+1)`), then `R(N) ≤ q(N)` at `A_pad = p + 1`. -/
theorem width_le_nativeWidth (k p C c : ℕ) (R : ℕ → ℕ)
    (hR : ∀ n, 1 ≤ n → 2 ^ R n ≤ C * (c * (n ^ (k + 2) + 1)) * logScale (c * (n ^ (k + 2) + 1)) ^ p) :
    ∃ N₀, ∀ N, N₀ ≤ N → R N ≤ Ledger.nativeWidth k (p + 1) N := by
  set M := Nat.clog 2 (c + 2) + 2 with hM
  set K := 2 * C * c * (M + 1) ^ p + 1 with hK
  refine ⟨2 ^ K + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 (2 ^ K)) hN
  set T := N ^ (k + 2) with hT
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ hN1
  set L := Nat.clog 2 T with hL
  -- `L ≥ K`: `T ≥ N ≥ 2^K`
  have hLK : K ≤ L := by
    have hNT : N ≤ T := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ (k + 2) := Nat.pow_le_pow_right hN1 (by omega)
    have h2K : 2 ^ K ≤ T := le_trans (le_trans (Nat.le_succ _) hN) hNT
    calc K = Nat.clog 2 (2 ^ K) := (Nat.clog_pow 2 K (by norm_num)).symm
      _ ≤ L := Nat.clog_mono_right 2 h2K
  -- the log scale is at most `(M+1)(L+2)`
  have hscale : logScale (c * (T + 1)) ≤ (M + 1) * (L + 2) := by
    unfold logScale
    have := clog_add_le c T hT1
    nlinarith
  -- `2^q ≥ T·(L+2)^{p+1}`
  have hq : T * (L + 2) ^ (p + 1) ≤ 2 ^ Ledger.nativeWidth k (p + 1) N := by
    unfold Ledger.nativeWidth
    rw [← hT, ← hL, show L + (p + 1) * Nat.clog 2 (L + 2) + (p + 1) = L + Nat.clog 2 (L + 2) * (p + 1) + (p + 1) by ring,
      pow_add 2 (L + Nat.clog 2 (L + 2) * (p + 1)) (p + 1), pow_add 2 L (Nat.clog 2 (L + 2) * (p + 1)),
      pow_mul 2 (Nat.clog 2 (L + 2)) (p + 1)]
    have h1 : T ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) T
    have h2 : L + 2 ≤ 2 ^ Nat.clog 2 (L + 2) := Nat.le_pow_clog (by norm_num) (L + 2)
    have h3 : (L + 2) ^ (p + 1) ≤ (2 ^ Nat.clog 2 (L + 2)) ^ (p + 1) := Nat.pow_le_pow_left h2 _
    have h4 : 1 ≤ 2 ^ (p + 1) := Nat.one_le_two_pow
    calc T * (L + 2) ^ (p + 1) ≤ 2 ^ L * (2 ^ Nat.clog 2 (L + 2)) ^ (p + 1) := Nat.mul_le_mul h1 h3
      _ ≤ 2 ^ L * (2 ^ Nat.clog 2 (L + 2)) ^ (p + 1) * 2 ^ (p + 1) := Nat.le_mul_of_pos_right _ h4
  have hbound := hR N hN1
  rw [← hT] at hbound
  have hlhs : C * (c * (T + 1)) * logScale (c * (T + 1)) ^ p ≤ T * (L + 2) ^ (p + 1) := by
    have hs := Nat.pow_le_pow_left hscale p
    rw [mul_pow] at hs
    have hT2 : T + 1 ≤ 2 * T := by omega
    calc C * (c * (T + 1)) * logScale (c * (T + 1)) ^ p
        ≤ C * (c * (2 * T)) * ((M + 1) ^ p * (L + 2) ^ p) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT2)) hs
      _ = T * (L + 2) ^ p * (2 * C * c * (M + 1) ^ p) := by ring
      _ ≤ T * (L + 2) ^ p * (L + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = T * (L + 2) ^ (p + 1) := by ring
  have hpow : 2 ^ R N ≤ 2 ^ Ledger.nativeWidth k (p + 1) N := hbound.trans (hlhs.trans hq)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hpow

end NearCubicWires.WireExponent3_5.Transfer
