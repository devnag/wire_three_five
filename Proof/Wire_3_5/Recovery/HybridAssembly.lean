import Proof.CaseAnalysis.CaseTwoDirect
import Proof.CaseAnalysis.NativeWidthStep
import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Recovery.RecoveryEventualBase
import Proof.Wire_3_5.Recovery.RecoveryLeaf
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Bindings.CLW20_Lemma3_8
import Proof.CaseAnalysis.CaseOneHardness
import Proof.CaseAnalysis.Parameters
import Proof.Wire_3_5.Recovery.RecoveryFamily
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule
import Proof.Wire_3_5.Recovery.CertSchedule

/-! # One source length of the hybrid recovery is hard in both classes (P3:3685-3733; D1.6)

Realizes the per-length hardness of the recovered language in its hybrid form: Case 1 at the refuter
hierarchy's native outer PCP of width `R = R(2^a)` ("If no size-`q^G` oracle makes the outer verifier a tautology [...]
Apply the imported worst-case amplifier", P3:3704-3709, with "`G/c_STV` exceeds a general-Boolean simulation exponent
[...] with a fixed positive margin", P3:3685-3692) and Case 2 at the union machine's padded request (P3:3710-3733).
Case 1's numerics now read the native width `R`, which is within a constant factor of `q`: `R(2^a) ≥ a + 1` (base's
`native_dyadic_lower`) and `q(2^a) ≤ K₁(a + 1)` with `K₁ = (k+2)(1+A_pad) + 3A_pad + 1`.

Paper quantities: `rpow_oracle_le` (`(q^{17c})^{−1/c} ≤ R^{−17}`), **`caseOne_sizeB`** (the size premises with the
envelope `n + cap + 2 ≤ B(R+1)⁴`), `eventually_caseOne_advR` (`(R^{17c})^{−1/c} < e_{t(q)}` once `q ≤ K₁R`),
`widthAt_le` (`q(2^a) ≤ K₁(a+1)`), and **`core_hard_at2`** (the hybrid core of one source length is below
`1/2 + e_{t(q)}` against every `SYM∘THR` / `THR∘THR` circuit within `⌊w_i(q)⌋` wires). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open Filter

/-! ## Case 1 at the native width -/

/-- **Case 1's size premises** with the envelope `n + cap + 2 ≤ B(R+1)⁴`. -/
theorem caseOne_sizeB (c : ℕ) (hc : 1 ≤ c) (R n cap K B : ℕ) (hK : K ≤ 50) (hR1 : 1 ≤ R)
    (hR : 50 * B ^ 4 * (R + 1) ^ 16 ≤ R ^ 17) (hn : n + cap + 2 ≤ B * (R + 1) ^ 4) :
    K * (n + cap + 2) ^ 4 ≤ integerFloorRoot c (RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R) := by
  apply le_integerFloorRoot (by omega)
  have h1 : K * (n + cap + 2) ^ 4 ≤ 50 * (B * (R + 1) ^ 4) ^ 4 :=
    Nat.mul_le_mul hK (Nat.pow_le_pow_left hn 4)
  have h2 : 50 * (B * (R + 1) ^ 4) ^ 4 = 50 * B ^ 4 * (R + 1) ^ 16 := by ring
  have h3 : K * (n + cap + 2) ^ 4 ≤ R ^ 17 := by omega
  calc (K * (n + cap + 2) ^ 4) ^ c ≤ (R ^ 17) ^ c := Nat.pow_le_pow_left h3 c
    _ = R ^ (17 * c) := by rw [← pow_mul]
    _ ≤ RecoveryScheduleEnvelope.oracleSizeBound (17 * c) R := oracleSize_ge _ R hR1

/-! ## One source length -/

/-- The width constant `K₁ = (k+2)(1+A_pad) + 3A_pad + 1` (`q(2^a) ≤ K₁(a+1)`). -/
def widthK (kclk Apad : ℕ) : ℕ := (kclk + 2) * (1 + Apad) + 3 * Apad + 1

section Assembly2

end Assembly2

end NearCubicWires.WireExponent3_5.Transfer
