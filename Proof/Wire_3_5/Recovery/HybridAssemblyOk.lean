import Proof.Wire_3_5.Recovery.HybridAssembly
import Proof.Wire_3_5.Recovery.HybridCoreOk

/-! # The hybrid core of one source length at the gate constants, from the atom test's completeness

Case 2 (P3:3711-3729) contradicts the union machine's rejection at the guess it constructs, which passes the atom test
("It rejects … oversized atoms", P3:3670). **`core_hard_at2_ok`** is `core_hard_at2` with completeness only at accepting
guesses WITH `AtomsOkG` (through `hybrid_bounds_ok`).

Paper quantity of the main type: the hybrid core's agreement with every small circuit in both classes. -/

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

section Assembly2Ok
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
  (P : FusedPrimitive (G.inputs kclk coef A a ha)) (M : OrdinaryWeakMachine)

include hG in
/-- **The hybrid core of one source length is hard in both classes** at the gate constants, from the atom test's completeness. -/
theorem core_hard_at2_ok {N : ℕ} (z : BitInput N) (q n R : ℕ)
    (hw : (recSetup2 l G kclk coef A a ha).pcp.nativeWidth N = q)
    (harity : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      ((recSetup2 l G kclk coef A a ha).request z oracle).arity = q)
    (hyes : recL l kclk N z = true) (hrej : ¬ M.accepts N z)
    (hacc : ∀ g : UnionGuess (recSetup2 l G kclk coef A a ha) z,
      UnionAccepts (recSetup2 l G kclk coef A a ha) P z g → AtomsOkG g → M.accepts N z)
    (hfit : (G.budget kclk coef A a ha).FitsAt q)
    (hbud : recBudget2 l kclk q ≤ N / 16)
    (hQ : RecQ l G q) (hKcl : (gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree ≤ q + 2)
    (hlen : recCopies (gateZeta_pos l) (gateZeta_lt l) q * (q + clauseWidth (recDG l) q + 1) ≤ n)
    (hn : n + 1 ≤ (q + 1) ^ 4)
    (hR : (recPCP l kclk).pcp.nativeWidth N = R) (hR1 : 1 ≤ R) (hRq : R ≤ q)
    (hqR : q ≤ widthK kclk G.Apad * R)
    (hRbig : 50 * (3 * widthK kclk G.Apad ^ 4 + 1) ^ 4 * (R + 1) ^ 16 ≤ R ^ 17)
    (hadvR : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * l.eightSources.amplification.stvExponent) R : ℝ)
      (-(1 : ℝ) / l.eightSources.amplification.stvExponent) <
      xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) :
    (∀ circuit : SymmetricThresholdCircuit n, circuit.wireCount ≤ ⌊wireCap G.row.cap .sym q⌋₊ →
      agreement circuit.eval (hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _)
        (gatePCPP l) (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z
        (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n) <
        1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) ∧
    (∀ circuit : ThresholdThresholdCircuit n, circuit.wireCount ≤ ⌊wireCap G.row.cap .thr q⌋₊ →
      agreement circuit.eval (hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _)
        (gatePCPP l) (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z
        (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n) <
        1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) := by
  have hc := l.eightSources.amplification.stvExponentPositive
  have hq1 : 1 ≤ q := by have := hQ.two; omega
  have hQ1 : 528 ≤ q + 1 := by have := hQ.big; omega
  -- the request's size, the clause bits, the oracle code, the guess budget
  have hsize : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      ((recSetup2 l G kclk coef A a ha).request z oracle).circuit.size + 1 ≤ recKs2 l kclk * (q + 1) ^ recSigma l := by
    intro oracle hs
    have h := requestSize2_le l G kclk coef A a ha z oracle hs
    calc _ ≤ recKs2 l kclk * ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N + 1) ^ recSigma l := h
      _ = recKs2 l kclk * (q + 1) ^ recSigma l := by rw [hw]
  have hcb : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup2 l G kclk coef A a ha).G
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).clauseBits ≤ clauseWidth (recDG l) q := by
    intro oracle hs
    have h1 := hsize oracle hs
    have hcc := (gatePCPP l).clauseCountBound ((recSetup2 l G kclk coef A a ha).request z oracle)
    apply clauseBits_le
    calc 2 ^ ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).clauseBits
        ≤ (gatePCPP l).coefficient *
            (((recSetup2 l G kclk coef A a ha).request z oracle).circuit.size + 1) ^ (gatePCPP l).degree := hcc
      _ ≤ (gatePCPP l).coefficient * (recKs2 l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = ((gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree) *
            (q + 1) ^ (recSigma l * (gatePCPP l).degree) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ (q + 2) * (q + 2) ^ (recSigma l * (gatePCPP l).degree) :=
          Nat.mul_le_mul hKcl (Nat.pow_le_pow_left (by omega) _)
      _ = (q + 2) ^ recDG l := by unfold recDG; ring
  have hO : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ recKo l q := by
    intro oracle hs
    have h1 : oracle.size + 1 ≤ (q + 1) ^ recOracleExp l :=
      calc oracle.size + 1 ≤ ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N + 1) ^
            2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) := oracleSize_le (recOracleDeg l) _ _ hs
        _ = (q + 1) ^ recOracleExp l := by rw [hw]; rfl
    have hg : q + 1 ≤ (q + 1) ^ recOracleExp l := Nat.le_self_pow (by unfold recOracleExp; positivity) _
    exact oracleCode_le oracle ((q + 1) ^ recOracleExp l + 4) (by omega) (by rw [hw]; omega) (by omega)
  have hbudget : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l)
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      1 + recKo l q + (((recSetup2 l G kclk coef A a ha).pcppOf z oracle).systematicBits +
        ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits) * (G.row.sp q * (4 + recKc q)) ≤ N / 16 := by
    intro oracle hs
    have h1 := hsize oracle hs
    have hsys : ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).systematicBits ≤
        (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree :=
      calc _ ≤ (gatePCPP l).coefficient * (((recSetup2 l G kclk coef A a ha).request z oracle).arity + 1) ^
            (gatePCPP l).degree := (gatePCPP l).systematicBound ((recSetup2 l G kclk coef A a ha).request z oracle)
        _ = (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree := by rw [harity oracle]
    have haux : ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits ≤
        (gatePCPP l).coefficient * (recKs2 l kclk * (q + 1) ^ recSigma l) ^ (gatePCPP l).degree :=
      ((gatePCPP l).auxiliaryBound ((recSetup2 l G kclk coef A a ha).request z oracle)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _))
    have hnv : ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).systematicBits +
        ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).auxiliaryBits ≤ recNv2 l kclk q := Nat.add_le_add hsys haux
    have hsp : G.row.sp q * (4 + recKc q) ≤ q * (4 + recKc q) := Nat.mul_le_mul_right _ hQ.sp
    calc _ ≤ 1 + recKo l q + recNv2 l kclk q * (q * (4 + recKc q)) :=
          Nat.add_le_add_left (Nat.mul_le_mul hnv hsp) _
      _ = recBudget2 l kclk q := rfl
      _ ≤ N / 16 := hbud
  -- the description envelopes
  have hLdS : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      restrictedSymmetricDescriptionCap ((recSetup2 l G kclk coef A a ha).request z oracle).arity
        (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
        (2 ^ symmetricDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity +
          clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊) ⌊wireCap G.row.cap .sym q⌋₊ ≤ (q + 1) ^ 26 := by
    intro oracle
    rw [harity oracle]
    have h := symLdesc_le (q + 1) (q + clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊ (by omega)
      (by have := hQ.cw; omega) hQ.capS.2
    simp only [Nat.add_sub_cancel] at h
    have h2 : 528 * (q + 1) ^ 12 ≤ (q + 1) ^ 26 :=
      calc 528 * (q + 1) ^ 12 ≤ (q + 1) * (q + 1) ^ 12 := Nat.mul_le_mul_right _ hQ1
        _ = (q + 1) ^ 13 := by ring
        _ ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact h.trans h2
  have hLdT : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      restrictedThresholdDescriptionCap ((recSetup2 l G kclk coef A a ha).request z oracle).arity
        (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
        (2 ^ thresholdDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity +
          clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊)
        (thresholdDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity +
          clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊) ≤ (q + 1) ^ 26 := by
    intro oracle
    rw [harity oracle]
    have h := thrLdesc_le (q + 1) (q + clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊ (by omega)
      (by have := hQ.cw; omega) hQ.capT.2
    simp only [Nat.add_sub_cancel] at h
    have h2 : 75894 * (q + 1) ^ 25 ≤ (q + 1) ^ 26 :=
      calc 75894 * (q + 1) ^ 25 ≤ (q + 1) * (q + 1) ^ 25 := Nat.mul_le_mul_right _ hQ.big
        _ = (q + 1) ^ 26 := by ring
    exact h.trans h2
  -- Case 2's ledgers
  have ledS : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup2 l G kclk coef A a ha).G
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      CaseTwoLedger (recSetup2 l G kclk coef A a ha) z oracle .sym P (gateCParams1 l)
        (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) ⌊wireCap G.row.cap .sym q⌋₊
        (restrictedSymmetricDescriptionCap ((recSetup2 l G kclk coef A a ha).request z oracle).arity
          (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
          (2 ^ symmetricDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity +
            clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊) ⌊wireCap G.row.cap .sym q⌋₊) := by
    intro oracle hs
    exact ledger_at2 l G hG kclk coef A a ha P .sym z oracle q (harity oracle) hq1 hQ.star hfit _
      (Nat.floor_le (wireCap_nonneg _ _ _)) hQ.capS.2 hQ.capS.1 hQ.sp _ (hLdS oracle)
      (by unfold restrictedSymmetricDescriptionCap; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      hQ.xi hQ.hD (recKo l q) (recKc q) (hO oracle hs)
      (fun C hd => atomCode_le .sym C ((q + 1) ^ 26 + 4) (by omega) (by have := hLdS oracle; omega))
      (hbudget oracle hs)
  have ledT : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup2 l G kclk coef A a ha).G
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      CaseTwoLedger (recSetup2 l G kclk coef A a ha) z oracle .thr P (gateCParams1 l)
        (massCap (gateCParams1 l).ζ (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) ⌊wireCap G.row.cap .thr q⌋₊
        (restrictedThresholdDescriptionCap ((recSetup2 l G kclk coef A a ha).request z oracle).arity
          (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1)
          (2 ^ thresholdDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity +
            clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊)
          (thresholdDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity +
            clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊)) := by
    intro oracle hs
    exact ledger_at2 l G hG kclk coef A a ha P .thr z oracle q (harity oracle) hq1 hQ.star hfit _
      (Nat.floor_le (wireCap_nonneg _ _ _)) hQ.capT.2 hQ.capT.1 hQ.sp _ (hLdT oracle)
      (by unfold restrictedThresholdDescriptionCap; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      hQ.xi hQ.hD (recKo l q) (recKc q) (hO oracle hs)
      (fun C hd => atomCode_le .thr C ((q + 1) ^ 26 + 4) (by omega) (by have := hLdT oracle; omega))
      (hbudget oracle hs)
  -- Case 1's conditions, at the native width `R`
  have hK1 : 1 ≤ widthK kclk G.Apad := by unfold widthK; omega
  have hq' : 1 ≤ (recPCP l kclk).pcp.nativeWidth N := by rw [hR]; exact hR1
  have hfit1 : ((selectedAmplifier l.eightSources.amplification (recOracleDeg l)).output
      (RecoveryCaseOneRequest.request (recPCP l kclk).pcp z).inputArity
      (RecoveryCaseOneRequest.request (recPCP l kclk).pcp z).function).arity ≤ n := by
    have hin : (RecoveryCaseOneRequest.request (recPCP l kclk).pcp z).inputArity = R := hR
    have h := CloseoutParameters.arity_envelope (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
      (recCopies (gateZeta_pos l) (gateZeta_lt l) q) _ (clauseWidth (recDG l) q) hQ.copies (by rw [hin]; exact hR1)
      (RecoveryCaseOneRequest.request (recPCP l kclk).pcp z).function
    refine h.trans (le_trans ?_ hlen)
    rw [hin]
    exact Nat.mul_le_mul_left _ (by omega)
  have hB : ∀ W : ℕ, W + 1 ≤ 2 * (q + 1) ^ 4 →
      n + W + 2 ≤ (3 * widthK kclk G.Apad ^ 4 + 1) * (R + 1) ^ 4 := by
    intro W hW
    have h1 : q + 1 ≤ widthK kclk G.Apad * (R + 1) := by
      have := Nat.mul_le_mul_left (widthK kclk G.Apad) (Nat.le_succ R)
      have e : widthK kclk G.Apad * (R + 1) = widthK kclk G.Apad * R + widthK kclk G.Apad := by ring
      omega
    have h2 : (q + 1) ^ 4 ≤ widthK kclk G.Apad ^ 4 * (R + 1) ^ 4 := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left h1 4
    have e : (3 * widthK kclk G.Apad ^ 4 + 1) * (R + 1) ^ 4 =
        3 * (widthK kclk G.Apad ^ 4 * (R + 1) ^ 4) + (R + 1) ^ 4 := by ring
    have h3 : 1 ≤ (R + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hsym1 : 40 * (n + ⌊wireCap G.row.cap .sym q⌋₊ + 2) ^ 4 ≤ integerFloorRoot
      l.eightSources.amplification.stvExponent (RecoveryScheduleEnvelope.oracleSizeBound
        (17 * l.eightSources.amplification.stvExponent) ((recPCP l kclk).pcp.nativeWidth N)) := by
    rw [hR]
    exact caseOne_sizeB _ hc R n _ 40 _ (by norm_num) hR1 hRbig (hB _ hQ.capS.2)
  have hthr1 : 50 * (n + ⌊wireCap G.row.cap .thr q⌋₊ + 2) ^ 4 ≤ integerFloorRoot
      l.eightSources.amplification.stvExponent (RecoveryScheduleEnvelope.oracleSizeBound
        (17 * l.eightSources.amplification.stvExponent) ((recPCP l kclk).pcp.nativeWidth N)) := by
    rw [hR]
    exact caseOne_sizeB _ hc R n _ 50 _ le_rfl hR1 hRbig (hB _ hQ.capT.2)
  have hadv1 : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * l.eightSources.amplification.stvExponent)
      ((recPCP l kclk).pcp.nativeWidth N) : ℝ) (-(1 : ℝ) / l.eightSources.amplification.stvExponent) <
      xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q) := by
    rw [hR]; exact hadvR
  -- Case 2's conditions
  have hcopies : 1 ≤ recCopies (gateZeta_pos l) (gateZeta_lt l) q := by unfold recCopies; omega
  have hz0 : (0 : ℝ) < ((gateCParams1 l).ζ : ℝ) := by exact_mod_cast gateZeta_pos l
  have hz1 : ((gateCParams1 l).ζ : ℝ) < 1 / 2 := by
    have h : (((gateCParams1 l).ζ : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr (gateZeta_lt l)
    rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have heps : xorEpsilon ((gateCParams1 l).ζ : ℝ) (recCopies (gateZeta_pos l) (gateZeta_lt l) q) <
      xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q) :=
    xorEpsilon_succ_lt _ hz0 hz1 _ (sched_spec (gateZeta_pos l) (gateZeta_lt l) (Lq q)).1
  have hfit2 : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recSetup2 l G kclk coef A a ha).G
        ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      recCopies (gateZeta_pos l) (gateZeta_lt l) q *
        (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseWidth (recDG l) q + 1) ≤ n := by
    intro oracle _
    rw [harity oracle]; exact hlen
  exact hybrid_bounds_ok l G P M z hacc hrej (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n
    ⌊wireCap G.row.cap .sym q⌋₊ ⌊wireCap G.row.cap .thr q⌋₊ _ hq' (recPCP_complete l kclk z hyes) hfit1 hsym1 hthr1
    hadv1 hcopies heps hcb hfit2 ledS ledT

end Assembly2Ok

end NearCubicWires.WireExponent3_5.Transfer
