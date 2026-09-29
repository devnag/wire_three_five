import Proof.Wire_3_5.Recovery.CaseTwoBudget

/-! # The hybrid Case-2 execution runs in `2^{O(n)}` (P3:3769-3771; D1.6 A3d)

Realizes, for the hybrid Case-2 execution of A3c (`CaseTwoExec.htwo`), "There are at most `2^{O(q)}` SAT queries and
local work, in addition to `poly(T(N_a)) = 2^{O(q)}` refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall"
(P3:3769-3771):
* **`foldNeed_cap`**: one capacity exponent `e₄` bounds the fold's bank need at every address length `n` (the need is a
  polynomial of `Env(N) + q` with `N ≤ 2^n`, `q ≤ n`; base `CloseoutCapacity.capacity` is `2^{e₄ n + e₄}`);
* **`htwoCost_poly`**: the whole execution's step bound `htwoCost` is at most `C·(2^n+1)^E` for fixed `C, E` (base's
  cold converter `ColdBudget.polynomial`, the hierarchy frame `Execution.frame_budget_bound`, `CertPrefix.prefixCost_le`, the scan's `scanRoundBound` caps, base's `CloseoutCapacity.budget_bound`, and A3d's block
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
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
  {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad)

/-- The fold's step budget over `c ≤ n` rounds. -/
theorem foldBudget_le (hcoeff : H.coefficient ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (degree D : ℕ)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    {N : ℕ} (point : BitInput N) (c C : ℕ) (hfit : c * widthOf source a H Cpad hpad r oracle q hq D ≤ N)
    (hcN : c ≤ N) :
    foldBudget source a H Cpad hpad r oracle q hq D point c C ≤
      N * (2 * q + 2 * C + 14 * N + 40 + blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q)) +
        N + 10 := by
  have hfc := foldCost_le source a H Cpad hpad r oracle q hq degree D hcoeff horacle hcb point c hfit
  have hin : foldCost source a H Cpad hpad r oracle q hq D point c + 1 +
      (2 * C + 4 + 1 + (2 * (c * widthOf source a H Cpad hpad r oracle q hq D) + 6)) + 2 ≤
      2 * q + 2 * C + 14 * N + 40 + blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) := by
    omega
  have hm := Nat.mul_le_mul hcN hin
  unfold foldBudget
  omega

open NearCubicWires.PaddedRunnerBudgetClosure in
/-- **One capacity exponent covers the fold's bank need**: `foldNeed ≤ 2^{e₄ n + e₄}` whenever the blocks fit in `n`,
`q ≤ n` and the source length is at most `2^n`. -/
theorem foldNeed_cap (hcoeff : H.coefficient ≤ Cpad) (degree D : ℕ) :
    ∃ e4 : ℕ, ∀ (r : InputRequest)
      (oracle : BooleanCircuit
        (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
      (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
      {N : ℕ} (point : BitInput N) (c : ℕ),
      oracle.size ≤ oracleSizeBound degree
        (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) →
      (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
        capOf source a H Cpad hpad r oracle q hq D →
      c * widthOf source a H Cpad hpad r oracle q hq D ≤ N → q ≤ N → r.1 ≤ 2 ^ N →
      foldNeed source a H Cpad hpad r oracle q hq D point c ≤ RepairSource.CloseoutCapacity.capacity e4 e4 N := by
  obtain ⟨Ee, Ce, hEe⟩ := WholeBudgetHierarchy.envelope_polynomial source a H Cpad degree
  have hp (c d : ℕ) : SourcePoly (fun x => c * (x + 1) ^ d) := sourcePoly_of_le c d fun _ => le_rfl
  have hf : SourcePoly (fun x => Ce * (x + 1) ^ Ee + x) := (hp Ce Ee).add sourcePoly_id
  obtain ⟨Eb, Cb, hBb⟩ := blockEnv_poly a D hf
  have hΨ : SourcePoly (fun x => 4 * (Ce * (x + 1) ^ Ee) + 20 * x + 40 + Cb * (x + 1) ^ Eb) :=
    ((((hp Ce Ee).const_mul 4).add (sourcePoly_id.const_mul 20)).add (polyDominated_const 40)).add (hp Cb Eb)
  obtain ⟨E2, C2, h2⟩ := hΨ
  refine ⟨natBitLength C2 + 2 * E2 + 1, fun r oracle q hq N point c horacle hcb hfit hqN hr => ?_⟩
  have hneed := foldNeed_le source a H Cpad hpad r oracle q hq degree D hcoeff horacle hcb point c hfit hqN
  have hEr : WholeBudgetHierarchy.envelope source a H Cpad degree r.1 ≤ Ce * (r.1 + 1) ^ Ee := hEe r.1
  have hEx : Ce * (r.1 + 1) ^ Ee ≤ Ce * (2 ^ N + 1) ^ Ee := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hN2 : N < 2 ^ N := Nat.lt_two_pow_self
  have hbe : blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) ≤ Cb * (2 ^ N + 1) ^ Eb :=
    (blockEnv_mono a D (show WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q ≤
      Ce * (2 ^ N + 1) ^ Ee + 2 ^ N by omega)).trans (hBb (2 ^ N))
  have hC2 : 4 * (Ce * (2 ^ N + 1) ^ Ee) + 20 * 2 ^ N + 40 + Cb * (2 ^ N + 1) ^ Eb ≤ C2 * (2 ^ N + 1) ^ E2 := h2 (2 ^ N)
  exact le_trans (by omega) (hC2.trans (poly_le_cap C2 E2 N))

open NearCubicWires.PaddedRunnerBudgetClosure in
/-- **The hybrid Case-2 execution runs in `2^{O(n)}`**: for fixed capacity exponents, `htwoCost ≤ C·(2^n+1)^E` at every
address length `n` whose `t + 1` blocks fit, at the width `q = q(2^S)` and the source length `≤ 2^n`. -/
theorem htwoCost_poly (hcoeff : H.coefficient ≤ Cpad) (A u v e1 e2 e3 e4 degree D : ℕ) :
    ∃ C E : ℕ, ∀ (r : InputRequest)
      (oracle : BooleanCircuit
        (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
      (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
      {N : ℕ} (point : BitInput N),
      oracle.size ≤ oracleSizeBound degree
        (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) →
      a.minimumArity ≤ q → q = widthAt k A (CertPrefix.prefixS k A u v D N) →
      (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
        capOf source a H Cpad hpad r oracle q hq D →
      (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) *
        widthOf source a H Cpad hpad r oracle q hq D ≤ N →
      r.1 ≤ 2 ^ N →
      scanRoundBound k A v D N N ((v - u) ^ 16) (v ^ 16) (pcap e1 N) (pcap e2 N) N + 1 ≤ pcap e3 N →
      htwoCost source a D H Cpad hpad r oracle q hq A u v e1 e2 e3 e4
        (oracleSizeBound degree
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
        point (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) ≤
        C * (2 ^ N + 1) ^ E := by
  have hc (v : ℕ) : SourcePoly (fun _ => v) := polyDominated_const v
  have hp (c d : ℕ) : SourcePoly (fun x => c * (x + 1) ^ d) := sourcePoly_of_le c d fun _ => le_rfl
  obtain ⟨Cc, Ec, _, hcold⟩ := ColdBudget.polynomial
  have hz := WholeBudgetHierarchy.clock_polynomial H
  have hw : SourcePoly (WholeBudgetHierarchy.width source H Cpad) :=
    hz.const_mul (HierarchySourceCost.widthCoefficient source H Cpad)
  have ho : SourcePoly (WholeBudgetHierarchy.oracleSize source H Cpad degree) :=
    sourcePoly_pow (hw.add (hc 1)) (2 ^ oracleDepth degree)
  have hG : SourcePoly (fun y => Cc * (WholeBudgetHierarchy.width source H Cpad y +
      WholeBudgetHierarchy.oracleSize source H Cpad degree y + 1) ^ Ec +
      (12 * y + 12 * WholeBudgetHierarchy.clockScale H y + 21)) :=
    ((sourcePoly_pow ((hw.add ho).add (hc 1)) Ec).const_mul Cc).add
      (((sourcePoly_id.const_mul 12).add (hz.const_mul 12)).add (hc 21))
  obtain ⟨Eg, Cg, hGb⟩ := hG
  obtain ⟨Ee, Ce, hEe⟩ := WholeBudgetHierarchy.envelope_polynomial source a H Cpad degree
  have hf : SourcePoly (fun x => Ce * (x + 1) ^ Ee + x) := (hp Ce Ee).add sourcePoly_id
  obtain ⟨Eb, Cb, hBb⟩ := blockEnv_poly a D hf
  have hΨ : SourcePoly (fun x => Cg * (x + 1) ^ Eg + CertPrefix.prefixCoef u v e1 e2 e3 * (x + 1) ^ (e1 + e2 + e3 + 4) +
      2 * (2 ^ e3 * (x + 1) ^ e3) + RepairSource.CloseoutCapacity.coefficient e4 e4 * (x + 1) ^ (e4 + 1) +
      2 * (2 ^ e4 * (x + 1) ^ e4) + 20 * x + 100 +
      x * (16 * x + 2 * (2 ^ e4 * (x + 1) ^ e4) + Cb * (x + 1) ^ Eb + 40)) :=
    (((((((hp Cg Eg).add (hp _ _)).add ((hp (2 ^ e3) e3).const_mul 2)).add (hp _ _)).add
      ((hp (2 ^ e4) e4).const_mul 2)).add (sourcePoly_id.const_mul 20)).add (hc 100)).add
      (sourcePoly_id.mul ((((sourcePoly_id.const_mul 16).add ((hp (2 ^ e4) e4).const_mul 2)).add (hp Cb Eb)).add
        (hc 40)))
  obtain ⟨E, C, hC⟩ := hΨ
  refine ⟨C, E, fun r oracle q hq N point horacle hmin hqS hcb hfit hr hTs' => ?_⟩
  -- the source dimensions (as in base's `Execution.budget_polynomial`)
  have hR : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤
      WholeBudgetHierarchy.width source H Cpad r.1 := by
    obtain ⟨_, he, _⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
    dsimp only [PCPPNativeHierarchyNodes.width]
    rw [he]
    exact HierarchySourceCost.width_bound source H Cpad hcoeff hpad r.1
  have hB : oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) ≤
      WholeBudgetHierarchy.oracleSize source H Cpad degree r.1 := by
    have hb := pairIter_add_one_le_pow (oracleDepth degree)
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
    have hpw := Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) (2 ^ oracleDepth degree)
    change pairIter (oracleDepth degree)
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) ≤
      (WholeBudgetHierarchy.width source H Cpad r.1 + 1) ^ (2 ^ oracleDepth degree)
    omega
  have hcold' := (hcold _ _ oracle horacle).trans (Nat.mul_le_mul_left Cc (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add hR hB) 1) Ec))
  have hfr := Execution.frame_budget_bound H r
  have hGr := hGb r.1
  simp only [ValidatorPolynomialDomination.PolyBounded] at hGr
  have hGx : Cg * (r.1 + 1) ^ Eg ≤ Cg * (2 ^ N + 1) ^ Eg := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  -- the widths
  have hwq := widthOf_eq source a D H Cpad hpad r oracle q hq hmin
  have hw1 : widthOf source a H Cpad hpad r oracle q hq D ≤
      (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) *
        widthOf source a H Cpad hpad r oracle q hq D := Nat.le_mul_of_pos_left _ (by omega)
  have hc1 : candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1 ≤
      (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) *
        widthOf source a H Cpad hpad r oracle q hq D := Nat.le_mul_of_pos_right _ (by omega)
  have hN2 : N < 2 ^ N := Nat.lt_two_pow_self
  -- the parameter stages
  have hS := CertPrefix.prefixS_le k A u v D N
  have hlen : (List.ofFn point).length = N := List.length_ofFn
  have hpar := paramCost_le k A u v D e1 e2 e3 (List.ofFn point)
  have hpre := CertPrefix.prefixCost_le k A u v D e1 e2 e3 (List.ofFn point) (by rw [hlen]; exact hTs')
  rw [hlen] at hpar hpre
  have hpsb := paramScanBound_le k A v D (CertPrefix.prefixS k A u v D N) N ((v - u) ^ 16) (v ^ 16) (pcap e1 N)
    (pcap e2 N) N hS
  have hpw := pwCost_le k A v D (CertPrefix.prefixS k A u v D N) N ((v - u) ^ 16) (v ^ 16) (pcap e1 N) (pcap e2 N) N
  rw [← hqS] at hpw
  have hcbm := candBound_mono k A v D (CertPrefix.prefixS k A u v D N) (N + 1) N ((v - u) ^ 16) (v ^ 16) (pcap e1 N)
    (pcap e2 N) N (by omega)
  have hsr : scanRoundBound k A v D N N ((v - u) ^ 16) (v ^ 16) (pcap e1 N) (pcap e2 N) N =
      candBound k A v D (N + 1) N ((v - u) ^ 16) (v ^ 16) (pcap e1 N) (pcap e2 N) N + 10 * N + 2 * pcap e1 N + 64 := rfl
  have hC3 : pcap e3 N ≤ 2 ^ e3 * (2 ^ N + 1) ^ e3 := cap_le_poly e3 N
  -- the capacity and the bank
  have hcap := RepairSource.CloseoutCapacity.budget_bound e4 e4 (List.ofFn point)
  rw [hlen] at hcap
  have hC4 := cap_le_poly e4 N
  have hfold := foldBudget_le source a H Cpad hpad hcoeff r oracle q hq degree D horacle hcb point
    (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1)
    (RepairSource.CloseoutCapacity.capacity e4 e4 N) hfit (by omega)
  have hEr : WholeBudgetHierarchy.envelope source a H Cpad degree r.1 ≤ Ce * (r.1 + 1) ^ Ee := hEe r.1
  have hEx : Ce * (r.1 + 1) ^ Ee ≤ Ce * (2 ^ N + 1) ^ Ee := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hbe : blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) ≤ Cb * (2 ^ N + 1) ^ Eb :=
    (blockEnv_mono a D (show WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q ≤
      Ce * (2 ^ N + 1) ^ Ee + 2 ^ N by omega)).trans (hBb (2 ^ N))
  have hprod := Nat.mul_le_mul hN2.le (show 2 * q + 2 * RepairSource.CloseoutCapacity.capacity e4 e4 N + 14 * N + 40 +
      blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) ≤
      16 * 2 ^ N + 2 * (2 ^ e4 * (2 ^ N + 1) ^ e4) + Cb * (2 ^ N + 1) ^ Eb + 40 by omega)
  have hCN := hC (2 ^ N)
  simp only [ValidatorPolynomialDomination.PolyBounded] at hCN
  refine le_trans ?_ hCN
  unfold htwoCost preCost PreparedFrames.budget initCost
  rw [hlen]
  omega

end Whole

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoCost
