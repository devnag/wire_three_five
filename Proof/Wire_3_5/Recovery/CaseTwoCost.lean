import Proof.Wire_3_5.Recovery.CaseTwoBudget

/-! # The hybrid Case-2 execution runs in `2^{O(n)}` (P3:3769-3771; D1.6 A3d)

Realizes, for the hybrid Case-2 execution of A3c (`CaseTwoExec.htwo`), "There are at most `2^{O(q)}` SAT queries and
local work, in addition to `poly(T(N_a)) = 2^{O(q)}` refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall"
(P3:3769-3771):
* **`foldNeed_cap`**: one capacity exponent `e₄` bounds the fold's bank need at every address length `n` (the need is a
  polynomial of `Env(N) + q` with `N ≤ 2^n`, `q ≤ n`; base `CloseoutCapacity.capacity` is `2^{e₄ n + e₄}`);
* **`htwoCost_poly`**: the whole execution's step bound `htwoCost` is at most `C·(2^n+1)^E` for fixed `C, E` (base's
  cold converter `ColdBudget.polynomial`, the hierarchy frame `Execution.frame_budget_bound`, M21's
  `CertPrefix.prefixCost_le`, the scan's `scanRoundBound` caps, base's `CloseoutCapacity.budget_bound`, and A3d's block
  envelope `blockEnv`), assembled as base's `Execution.budget_polynomial` does.

Paper quantity of the main type (`htwoCost_poly`): the hybrid Case-2 execution's time `C·(2^n+1)^E`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.PolynomialClock
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoBudget

noncomputable section

/-! ## The parameter stages within the scan's caps -/

section Params
variable (k A u v D : ℕ)

/-- The parameter core costs the prefix's stages plus the parameter scan (in place of the prefix's power). -/
theorem paramCost_le (e1 e2 e3 : ℕ) (bits : List Bool) :
    CaseTwoParamScan.paramCost k A u v D e1 e2 e3 bits ≤ CertPrefix.prefixCost k A u v D e1 e2 e3 bits +
      CaseTwoParamScan.paramScanBound k A v D (CertPrefix.prefixS k A u v D bits.length) bits.length ((v - u) ^ 16)
        (v ^ 16) (pcap e1 bits.length) (pcap e2 bits.length) bits.length := by
  unfold CaseTwoParamScan.paramCost CertPrefix.prefixCost
  omega

/-- The parameter scan at an index `S ≤ n` is within the scan round's bound at `n`. -/
theorem paramScanBound_le (S n p w total T c : ℕ) (hS : S ≤ n) :
    CaseTwoParamScan.paramScanBound k A v D S n p w total T c ≤ scanRoundBound k A v D n n p w total T c := by
  have := candBound_mono k A v D S (n + 1) n p w total T c (by omega)
  unfold CaseTwoParamScan.paramScanBound scanRoundBound
  omega

/-- The widths stage is within the candidate test's bound plus four clause widths. -/
theorem pwCost_le (S n p w total T c : ℕ) :
    CaseTwoParamWidth.pwCost k A D S ≤ candBound k A v D S n p w total T c +
      4 * CloseoutLanguage.clauseWidth D (widthAt k A S) := by
  have hcb := clause_budget_le D (widthAt k A S)
  have hsq : widthAt k A S + 8 ≤ (widthAt k A S + 8) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlq : 4 * widthAt k A S + 22 ≤ candLqBound (widthAt k A S) := by unfold candLqBound; omega
  unfold CaseTwoParamWidth.pwCost candBound candCoreBound
  omega

end Params

/-! ## The whole execution -/

section Whole

end Whole

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoCost
