import Lean
import Proof.Wire_3_5.Recovery.HybridLeaf
import Proof.Wire_3_5.Recovery.HybridLedgerOk
import Proof.Wire_3_5.Recovery.RecoveryCaseTwoOk
import Proof.Wire_3_5.Recovery.RecoveryLedgerAt
import Proof.Wire_3_5.Recovery.RecoveryEventual
import Proof.Wire_3_5.Recovery.RecoveryBudget
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Outer35.LenFit
import W3.Outer3.HardnessParts
import Proof.Wire_3_5.Recovery.HybridAssembly
import Proof.Wire_3_5.Recovery.RecoveryLeaf
import Proof.Wire_3_5.Recovery.RecoveryBudgetBase
import Proof.Wire_3_5.Transfer.TransferTargets


/-! # The recovered language is hard in both classes (the leaf hardness; §H.6, Theorem 1.1 row B)

Realizes the hardness half of the recovery leaf: at every large length `n` the slice `F_n` of the recovered language is
the three-way core at the refuter's word `z` (a hierarchy yes-instance that the union machine rejects), and it is hard
for every `SYM∘THR` and `THR∘THR` circuit within the row-B wire caps:
* **Case 1a (Hard word)** and **Case 1b (Hard oracle)** (§H.5): `X_z` (resp. `Ô*`) has no circuit of `q^G` gates, so
  its amplified and padded form has agreement below `1/2 + γ` (the amplifier, at the simulation bound);
* the exceptional length (a source circuit but no accepted outer oracle) does not occur: the first source circuit fits
  `λ_a` and passes the source check, so the short PCP's completeness gives an accepted oracle (Lemma H.7(d));
* **Case 2 (Hard proof table)** (§H.5; Lemma H.4): the pair `Γ* = (Γ*_src, Γ*_pf)` passes the outer step's guards
  (`PairGuards`) and `H_{Γ*}` is a tautology, so a sampled XOR sum under the caps would give an accepting guess at `z`,
  which the refuter forbids; the XOR lemma and the padding finish.

Main declarations: the guess-length envelope of the outer step (`recKoP`, `recNv3`, `recBudget3`, `recBudget3_poly`,
`pairWord_length_le`), **`eventually_slice3Ok`** (every large slice is hard), **`recLanguageCut2_hardOk`** (row B's
`ThrHardAt` / `SymHardAt`), and **`recoveryLeaf2Ok`** (the recovery leaf at the live setup, from an `E^NP` certificate). -/

set_option autoImplicit false
set_option maxRecDepth 120000


noncomputable section

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth paddedUnsigned)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open NearCubicWires.CircuitRestriction NearCubicWires.RepairXor NearCubicWires.ComponentwiseTransfer
open NearCubicWires.RecoveryPipeline (padCore)
open _root_.NearCubicWires.RepairSource (selectedAmplifier)
open Filter

/-! ## The guess-length envelope of the outer step -/

section Budget3
variable (l : Literals)

/-- The code bound of the pair field: `|pairWord Γ| ≤ K_O(q)` for two circuits of size `≤ q^G`. -/
def recKoP (q : ℕ) : ℕ := 4 * recKo l q + 1

/-- The PCPP variable count bound at `|H_Γ| + 1 ≤ K_s (q+1)^{e_H}` (Lemma H.7(b)). -/
def recNv3 (Ks q : ℕ) : ℕ :=
  (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree +
    (gatePCPP l).coefficient * (Ks * (q + 1) ^ eH l) ^ (gatePCPP l).degree

/-- **The guess-length envelope** `1 + K_O + n_v·q·(4 + K_c)` of the outer step. -/
def recBudget3 (Ks q : ℕ) : ℕ := 1 + recKoP l q + recNv3 l Ks q * (q * (4 + recKc q))

/-- **The guess-length envelope is a fixed polynomial of `q`.** -/
theorem recBudget3_poly (Ks : ℕ) : PolynomiallyBounded (recBudget3 l Ks) := by
  have hO : PolynomiallyBounded (recKo l) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_comp PCPPQueryBounds.circuit_polynomial (pb_succ_pow (recOracleExp l) 4)))
      (polynomiallyBounded_constant 1)
  have hOP : PolynomiallyBounded (recKoP l) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 4) hO)
      (polynomiallyBounded_constant 1)
  have hS : PolynomiallyBounded (fun q => canonicalSymmetricCircuitCodeBitBound ((q + 1) ^ 26 + 4)) :=
    polynomiallyBounded_comp SourceBudget.symWidth_poly (pb_succ_pow 26 4)
  have hT : PolynomiallyBounded (fun q => canonicalThresholdCircuitCodeBitBound ((q + 1) ^ 26 + 4)) :=
    polynomiallyBounded_comp SourceBudget.thrWidth_poly (pb_succ_pow 26 4)
  have hKc : PolynomiallyBounded recKc :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_add hS hT)) (polynomiallyBounded_constant 1)
  have hA : PolynomiallyBounded (fun q => (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant _) (pb_succ_pow' _)
  have hB : PolynomiallyBounded
      (fun q => (gatePCPP l).coefficient * (Ks * (q + 1) ^ eH l) ^ (gatePCPP l).degree) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant _)
      (polynomiallyBounded_pow (polynomiallyBounded_mul (polynomiallyBounded_constant _) (pb_succ_pow' _)) _)
  have hNv : PolynomiallyBounded (recNv3 l Ks) := polynomiallyBounded_add hA hB
  have hQ : PolynomiallyBounded (fun q => q * (4 + recKc q)) :=
    polynomiallyBounded_mul polynomiallyBounded_id (polynomiallyBounded_add (polynomiallyBounded_constant 4) hKc)
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_constant 1) hOP)
    (polynomiallyBounded_mul hNv hQ)

open NearCubicWires.WireExponent3_5.UnionMachine.Front35 in
/-- The pair field's length: twice the payload plus one. -/
theorem pairWord_length {q : ℕ} (B : NearCubicGates.Close.Outer.OuterGuess q) :
    (pairWord B).length = 2 * (pairRaw B).length + 1 := by
  have h := congrArg List.length (rawOf_pairRaw B)
  unfold rawOf at h
  rw [_root_.NearCubicWires.RepairOrdinary.SignedSortKey.binary_length] at h
  unfold pairWord
  rw [_root_.NearCubicWires.Bindings.Williams14.natWord_length, h]

open NearCubicWires.WireExponent3_5.UnionMachine.Front35 in
/-- **The pair field is within `K_O(q)`** when both circuits have at most `q^G` gates. -/
theorem pairWord_length_le {q : ℕ} (B : NearCubicGates.Close.Outer.OuterGuess q)
    (hs : B.src.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q)
    (hp : B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q) :
    (pairWord B).length ≤ recKoP l q := by
  have hcap : ∀ c : BooleanCircuit q, c.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q →
      (natWord (ExecutableInterfaces.encodeBooleanCircuit c)).length ≤ recKo l q := by
    intro c hc
    have h1 := oracleSize_le l q c.size hc
    have hg : q + 1 ≤ (q + 1) ^ capExp l := Nat.le_self_pow (by have := one_le_capExp l; omega) _
    exact oracleCode_le c ((q + 1) ^ recOracleExp l + 4) (by omega) (by
      show q ≤ (q + 1) ^ capExp l + 4; omega) (by show c.size ≤ (q + 1) ^ capExp l + 4; omega)
  have h1 := hcap B.src hs
  have h2 := hcap B.pf hp
  rw [pairWord_length]
  unfold pairRaw recKoP
  rw [List.length_append]
  omega

end Budget3

/-! ## Every large slice is hard -/

section Leaf3
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) {coef A a : ℕ} {ha : a ≤ kclk + 1}
  (U : Split.UnionLeafAt2 (G.inputs kclk coef A a ha) (unionSetupS2 l G kclk coef A a ha))
  (P : FusedPrimitive (G.inputs kclk coef A a ha))

/-- The width of the slice grows without bound. -/
theorem tendsto_sliceWidth : Tendsto (sliceWidth l) atTop atTop :=
  (tendsto_nativeWidth kclk (gateApad l)).comp (tendsto_two_pow_sourceIdx (recSched l))

include hG in
/-- **Every large slice of the recovered language is hard in both classes** within the integer wire caps. -/
theorem eventually_slice3Ok :
    ∀ᶠ n : ℕ in atTop,
      (∀ circuit : SymmetricThresholdCircuit n,
        circuit.wireCount ≤ ⌊wireCap G.row.cap .sym (sliceWidth l n)⌋₊ →
        agreement circuit.eval (recLanguage2 l (recMachine2Ok l G U P) n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (sliceWidth l n))) ∧
      (∀ circuit : ThresholdThresholdCircuit n,
        circuit.wireCount ≤ ⌊wireCap G.row.cap .thr (sliceWidth l n)⌋₊ →
        agreement circuit.eval (recLanguage2 l (recMachine2Ok l G U P) n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (sliceWidth l n))) := by
  have hc := l.eightSources.amplification.stvExponentPositive
  set S := recSetup2 l G kclk coef A a ha with hSdef
  set M := recMachine2Ok l G U P with hMdef
  obtain ⟨onR, hR⟩ := rejected_yes_eventually2Ok l G U P
  obtain ⟨onC, hC⟩ := complete2Ok l G U P
  obtain ⟨a₀, hfit₀⟩ := lenFit35 l
  obtain ⟨q₀, hcl₀⟩ := clauseBits_le l
  obtain ⟨Ks, hKs⟩ := datSize_le l
  obtain ⟨cB, dB, _, hBpoly⟩ := recBudget3_poly l Ks
  -- the source index past every onset
  have hsrc : ∀ᶠ n : ℕ in atTop, 1 + S.onset + (gateSV l).onset + a₀ ≤ (recSched l).sourceIdx n :=
    (recSched l).tendsto_sourceIdx.eventually (eventually_ge_atTop _)
  -- the facts at the source length `N = 2^s`
  have hNev : ∀ᶠ N : ℕ in atTop, onR ≤ N ∧ onC ≤ N ∧ (G.budget kclk coef A a ha).onset ≤ N ∧
      cB * (nativeWidth kclk (gateApad l) N + 1) ^ dB ≤ N / 16 := by
    filter_upwards [eventually_ge_atTop onR, eventually_ge_atTop onC,
      eventually_ge_atTop (G.budget kclk coef A a ha).onset,
      eventually_poly_le_div16 kclk (gateApad l) cB dB] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- the facts at the width `q`
  have hqev : ∀ᶠ q : ℕ in atTop, RecQ l G q ∧ q₀ + (gatePCPP l).minimumArity + 6 * ((recSched l).J + 1) + 2 ≤ q :=
    (eventually_recQ l G hG).and (eventually_ge_atTop _)
  filter_upwards [hsrc, (tendsto_two_pow_sourceIdx (recSched l)).eventually hNev,
    (tendsto_sliceWidth l).eventually hqev, (recSched l).eventually_lengths] with n hsn hNn hqn hlen
  obtain ⟨hRn, hCn, hBn, hbud⟩ := hNn
  obtain ⟨hQ, hqbig⟩ := hqn
  obtain ⟨-, hlen2, -, hnq⟩ := hlen
  set s := (recSched l).sourceIdx n with hsdef
  set q := sliceWidth l n with hqdef
  set z := (recRefuter l kclk).output M (2 ^ s) with hzdef
  have hqw : gateWidth l (2 ^ s) = q := rfl
  have hs1 : 1 ≤ s := by omega
  have hsq : s < q := W3.NearCubicWires.RepairSource.Outer3.nu_lt_width (gateMW l) (gateSV l) s
  have hq1 : 1 ≤ q := by omega
  have hlog : Nat.log 2 (2 ^ s) = s := Nat.log_pow (by norm_num) s
  have hcopies : 1 ≤ recCopies (gateZeta_pos l) (gateZeta_lt l) q := by unfold recCopies; omega
  have hn1 : n + 1 ≤ (q + 1) ^ 4 := n_succ_le _ q n (by omega) hnq
  have hfitT : recCopies (gateZeta_pos l) (gateZeta_lt l) q * (q + clauseWidth (recDG l) q + 1) ≤ n :=
    hlen2.trans (Nat.div_le_self _ _)
  have hz0 := gateZeta_pos l
  have hz1 := gateZeta_lt l
  have hz0' : (0 : ℝ) < ((gateCParams1 l).ζ : ℝ) := by exact_mod_cast hz0
  have hz1' : ((gateCParams1 l).ζ : ℝ) < 1 / 2 := by
    have h : (((gateCParams1 l).ζ : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hz1
    rw [show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at h
    exact h
  have heps : xorEpsilon ((gateCParams1 l).ζ : ℝ) (recCopies (gateZeta_pos l) (gateZeta_lt l) q) <
      xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q) :=
    xorEpsilon_succ_lt _ hz0' hz1' _ (sched_spec (gateZeta_pos l) (gateZeta_lt l) (Lq q)).1
  -- the refuter's word: a hierarchy yes-instance that the machine rejects; the machine accepts every accepting guess
  obtain ⟨hyesL, hrej⟩ := hR (2 ^ s) hRn
  have hyes : (gateH l).verifier.language (gateH l).time (2 ^ s) z := (refH_spec l kclk (2 ^ s) z).1 hyesL
  have hacc : ∀ g : UnionGuess S z, UnionAccepts S P z g → AtomsOkG g → M.accepts (2 ^ s) z :=
    fun g hg hok => hC (2 ^ s) hCn z g hg hok
  -- the slice is the three-way core at `(s, z)`
  have hslice : recLanguage2 l M n =
      W3.NearCubicWires.RepairSource.Outer3.coreC (gateMW l) (gateSV l) (gatePCPP l)
        l.eightSources.amplification.schedule s z
        (recCopies (gateZeta_pos l) (gateZeta_lt l) q) (clauseWidth (recDG l) q) n :=
    recLanguage2_eq l M n
  rw [hslice]
  -- Case 1: a worst-case hard function on `q` inputs, amplified and padded to `n`
  have caseOne : ∀ f : BoolFunction q, WorstCaseHardAt f (RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q) →
      (∀ circuit : SymmetricThresholdCircuit n, circuit.wireCount ≤ ⌊wireCap G.row.cap .sym q⌋₊ →
        agreement circuit.eval (NearCubicGates.Close.Transfer.GateParams.amplified
          l.eightSources.amplification.schedule q f n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) ∧
      (∀ circuit : ThresholdThresholdCircuit n, circuit.wireCount ≤ ⌊wireCap G.row.cap .thr q⌋₊ →
        agreement circuit.eval (NearCubicGates.Close.Transfer.GateParams.amplified
          l.eightSources.amplification.schedule q f n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)) := by
    intro f hardf
    have hfitAmp : (l.eightSources.amplification.schedule.output q f).arity ≤ n :=
      (CloseoutParameters.arity_envelope _ _ q (clauseWidth (recDG l) q) hQ.copies hq1 f).trans hfitT
    have hR17 : 50 * 4 ^ 4 * (q + 1) ^ 16 ≤ q ^ 17 := by have := hQ.pow17; norm_num; exact this
    have hsym := caseOne_sizeB l.eightSources.amplification.stvExponent (by omega) q n ⌊wireCap G.row.cap .sym q⌋₊ 40 4 (by norm_num) hq1 hR17
      (by have := hQ.capS.2; omega)
    have hthr := caseOne_sizeB l.eightSources.amplification.stvExponent (by omega) q n ⌊wireCap G.row.cap .thr q⌋₊ 50 4 le_rfl hq1 hR17
      (by have := hQ.capT.2; omega)
    exact W3.NearCubicWires.RepairSource.Outer3.amplified_hard _ f hq1 hardf l.eightSources.normalization
      ⌊wireCap G.row.cap .sym q⌋₊ ⌊wireCap G.row.cap .thr q⌋₊ hfitAmp hsym hthr _ hQ.adv1
  by_cases h1 : W3.NearCubicWires.RepairSource.Outer3.SrcExists (gateMW l) (gateSV l) (oracleDeg l) s z
  · by_cases h2 : W3.NearCubicWires.RepairSource.Outer3.AcceptedOracle (gateMW l) (gateSV l) (oracleDeg l) s z h1
    · by_cases h3 : W3.NearCubicWires.RepairSource.Outer3.IsCaseTwo (gateMW l) (gateSV l) (oracleDeg l) s z
      · -- Case 2 (Hard proof table): `Γ* = (Γ*_src, Γ*_pf)` passes the guards and `H_{Γ*}` is a tautology
        set B := W3.NearCubicWires.RepairSource.Outer3.selectedPair (gateMW l) (gateSV l) (oracleDeg l) s z h3 with hB
        have hBsrc : B.src.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q :=
          (_root_.NearCubicWires.RepairSource.RecoveryChoice.oracleSelector
            (W3.NearCubicWires.RepairSource.Outer3.checkPCP (gateMW l) (gateSV l) s z) (oracleDeg l) z h3.1).sizeBounded
        have hBpf : B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q :=
          (_root_.NearCubicWires.RepairSource.RecoveryChoice.oracleSelector _ (oracleDeg l) z h3.2.2.2).sizeBounded
        have hq0 : (gatePCPP l).minimumArity ≤ q := by omega
        have hcheckB : NearCubicGates.Close.Outer.Check s z B.src :=
          (NearCubicGates.Close.ENP.unitOuter_check s _ _ z z _ (fun _ => false)).mp
            ((_root_.NearCubicWires.RepairSource.RecoveryChoice.oracleSelector
              (W3.NearCubicWires.RepairSource.Outer3.checkPCP (gateMW l) (gateSV l) s z) (oracleDeg l) z h3.1).accepts
              (fun _ => false))
        have hguards : PairGuards S z B := by
          unfold PairGuards
          refine ⟨rfl, by rw [hlog], by rw [hlog]; omega, hBsrc,
            hBpf, ?_, ?_⟩
          · rw [hlog]; exact hfit₀ s (by omega) B.src hBsrc
          · rw [hlog]; exact (NearCubicGates.Close.Outer.check_iff_checkAt s z B.src).1 hcheckB
        have hreq : S.request z B = W3.NearCubicWires.RepairSource.Outer3.requestOf (gateMW l) (gateSV l) (gatePCPP l) s B
            hq0 := by
          show W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (recSV l kclk) (gatePCPP l) (Nat.log 2 (2 ^ s)) B
            = _
          rw [hlog]
          exact W3.NearCubicWires.RepairSource.Outer3.requestAt_of (gateMW l) (gateSV l) (gatePCPP l) s B hq0
        have harity : (S.request z B).arity = q := by rw [hreq]; rfl
        have htaut : ∀ x, (S.request z B).circuit.eval x = true := by
          rw [hreq]
          intro x
          exact W3.NearCubicWires.RepairSource.Outer3.selected_taut (gateMW l) (gateSV l) (oracleDeg l) s z h3 x
        -- the clause bound (at the request's own index `⌊log₂ 2^s⌋` and at `s`)
        have hr : (S.pcppOf z B).clauseBits ≤ clauseWidth (recDG l) q :=
          hcl₀ (Nat.log 2 (2 ^ s)) (2 ^ s) B (by rw [hlog]; exact hs1) (by rw [hlog]; exact hsq.le) (by omega) hBpf
        have hcs : ((gatePCPP l).output (W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l) (gatePCPP l)
            s B)).clauseBits ≤ clauseWidth (recDG l) q :=
          hcl₀ s (2 ^ s) B hs1 hsq.le (by omega) hBpf
        -- the request's size, the guess budget, the description envelopes, the ledgers
        have hsz : (S.request z B).circuit.size + 1 ≤ Ks * (q + 1) ^ eH l := by
          rw [hreq]; exact hKs s (2 ^ s) B hs1 hsq.le hBpf
        have hbudget : 1 + recKoP l q + ((S.pcppOf z B).systematicBits + (S.pcppOf z B).auxiliaryBits) *
            (G.row.sp q * (4 + recKc q)) ≤ 2 ^ s / 16 := by
          have hsys : (S.pcppOf z B).systematicBits ≤ (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree :=
            calc _ ≤ (gatePCPP l).coefficient * ((S.request z B).arity + 1) ^ (gatePCPP l).degree :=
                  (gatePCPP l).systematicBound (S.request z B)
              _ = (gatePCPP l).coefficient * (q + 1) ^ (gatePCPP l).degree := by rw [harity]
          have haux : (S.pcppOf z B).auxiliaryBits ≤
              (gatePCPP l).coefficient * (Ks * (q + 1) ^ eH l) ^ (gatePCPP l).degree :=
            ((gatePCPP l).auxiliaryBound (S.request z B)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz _))
          have hnv : (S.pcppOf z B).systematicBits + (S.pcppOf z B).auxiliaryBits ≤ recNv3 l Ks q :=
            Nat.add_le_add hsys haux
          have hsp : G.row.sp q * (4 + recKc q) ≤ q * (4 + recKc q) := Nat.mul_le_mul_right _ hQ.sp
          calc _ ≤ 1 + recKoP l q + recNv3 l Ks q * (q * (4 + recKc q)) :=
                Nat.add_le_add_left (Nat.mul_le_mul hnv hsp) _
            _ = recBudget3 l Ks q := rfl
            _ ≤ cB * (q + 1) ^ dB := hBpoly q
            _ ≤ 2 ^ s / 16 := hbud
        have hfitG : (G.budget kclk coef A a ha).FitsAt q := by
          have h := (G.budget kclk coef A a ha).fits (2 ^ s) hBn
          have e : (G.budget kclk coef A a ha).q (2 ^ s) = q := by
            show nativeWidth kclk G.Apad (2 ^ s) = nativeWidth kclk (gateApad l) (2 ^ s)
            rw [hG.apad]
          rw [e] at h
          exact h
        have hQ1 : 528 ≤ q + 1 := by have := hQ.big; omega
        have hLdS : restrictedSymmetricDescriptionCap (S.request z B).arity
            ((S.request z B).arity + clauseWidth (recDG l) q + 1)
            (2 ^ symmetricDescriptionCap ((S.request z B).arity + clauseWidth (recDG l) q + 1)
              ⌊wireCap G.row.cap .sym q⌋₊) ⌊wireCap G.row.cap .sym q⌋₊ ≤ (q + 1) ^ 26 := by
          rw [harity]
          have h := symLdesc_le (q + 1) (q + clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .sym q⌋₊ (by omega)
            (by have := hQ.cw; omega) hQ.capS.2
          simp only [Nat.add_sub_cancel] at h
          have h2 : 528 * (q + 1) ^ 12 ≤ (q + 1) ^ 26 :=
            calc 528 * (q + 1) ^ 12 ≤ (q + 1) * (q + 1) ^ 12 := Nat.mul_le_mul_right _ hQ1
              _ = (q + 1) ^ 13 := by ring
              _ ≤ (q + 1) ^ 26 := Nat.pow_le_pow_right (by omega) (by norm_num)
          exact h.trans h2
        have hLdT : restrictedThresholdDescriptionCap (S.request z B).arity
            ((S.request z B).arity + clauseWidth (recDG l) q + 1)
            (2 ^ thresholdDescriptionCap ((S.request z B).arity + clauseWidth (recDG l) q + 1)
              ⌊wireCap G.row.cap .thr q⌋₊)
            (thresholdDescriptionCap ((S.request z B).arity + clauseWidth (recDG l) q + 1)
              ⌊wireCap G.row.cap .thr q⌋₊) ≤ (q + 1) ^ 26 := by
          rw [harity]
          have h := thrLdesc_le (q + 1) (q + clauseWidth (recDG l) q + 1) ⌊wireCap G.row.cap .thr q⌋₊ (by omega)
            (by have := hQ.cw; omega) hQ.capT.2
          simp only [Nat.add_sub_cancel] at h
          have h2 : 75894 * (q + 1) ^ 25 ≤ (q + 1) ^ 26 :=
            calc 75894 * (q + 1) ^ 25 ≤ (q + 1) * (q + 1) ^ 25 := Nat.mul_le_mul_right _ hQ.big
              _ = (q + 1) ^ 26 := by ring
          exact h.trans h2
        have hO := pairWord_length_le l B hBsrc hBpf
        have ledS := ledger_at l G hG kclk coef A a ha P .sym z B q harity hq1 hQ.star hfitG _
          (Nat.floor_le (wireCap_nonneg _ _ _)) hQ.capS.2 hQ.capS.1 hQ.sp _ hLdS
          (by unfold restrictedSymmetricDescriptionCap; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
          hQ.xi hQ.hD (recKoP l q) (recKc q) hO
          (fun C hd => atomCode_le .sym C ((q + 1) ^ 26 + 4) (by omega) (by omega)) hbudget
        have ledT := ledger_at l G hG kclk coef A a ha P .thr z B q harity hq1 hQ.star hfitG _
          (Nat.floor_le (wireCap_nonneg _ _ _)) hQ.capT.2 hQ.capT.1 hQ.sp _ hLdT
          (by unfold restrictedThresholdDescriptionCap; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
          hQ.xi hQ.hD (recKoP l q) (recKc q) hO
          (fun C hd => atomCode_le .thr C ((q + 1) ^ 26 + 4) (by omega) (by omega)) hbudget
        -- no sampled XOR sum under the caps; the XOR lemma and the padding
        have hs := no_sampled_sym_ok S z B l.eightSources.normalization l.eightSources.expander P (gateCParams1 l) M
          hacc hrej hguards htaut (clauseWidth (recDG l) q) (recCopies (gateZeta_pos l) (gateZeta_lt l) q)
          ⌊wireCap G.row.cap .sym q⌋₊ hr (gateCParams1 l).ζ hz0 hz1 le_rfl ledS
        have ht := no_sampled_thr_ok S z B l.eightSources.normalization l.eightSources.expander P (gateCParams1 l) M
          hacc hrej hguards htaut (clauseWidth (recDG l) q) (recCopies (gateZeta_pos l) (gateZeta_lt l) q)
          ⌊wireCap G.row.cap .thr q⌋₊ hr (gateCParams1 l).ζ hz0 hz1 le_rfl ledT
        have hfit2 : recCopies (gateZeta_pos l) (gateZeta_lt l) q *
            ((S.request z B).arity + clauseWidth (recDG l) q + 1) ≤ n := by rw [harity]; exact hfitT
        have hsX := CloseoutLanguage.xor_hardness_from_sampled
          _root_.NearCubicWires.Bindings.CLW20Lemma38.clw20_xor_source (gateCParams1 l).ζ hz0 hz1
          symmetricWireFamily symmetricWireFamily_literalProjectionClosed symmetricWireFamily_negationClosed _
          (by omega) _ ⌊wireCap G.row.cap .sym q⌋₊ hcopies hs
        have htX := CloseoutLanguage.xor_hardness_from_sampled
          _root_.NearCubicWires.Bindings.CLW20Lemma38.clw20_xor_source (gateCParams1 l).ζ hz0 hz1
          thresholdWireFamily thresholdWireFamily_literalProjectionClosed thresholdWireFamily_negationClosed _
          (by omega) _ ⌊wireCap G.row.cap .thr q⌋₊ hcopies ht
        have hsP := averageHard_padCore (family := symmetricWireFamily) (size := ⌊wireCap G.row.cap .sym q⌋₊)
          symmetricWireFamily_restrictionClosed hsX hfit2
        have htP := averageHard_padCore (family := thresholdWireFamily) (size := ⌊wireCap G.row.cap .thr q⌋₊)
          thresholdWireFamily_restrictionClosed htX hfit2
        -- the core's value: the same padded XOR power, at the index `s = ⌊log₂ 2^s⌋`
        have htT : recCopies (gateZeta_pos l) (gateZeta_lt l) q *
            ((W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l) (gatePCPP l) s B).arity +
              clauseWidth (recDG l) q + 1) ≤ n := by
          rw [W3.NearCubicWires.RepairSource.Outer3.requestAt_of (gateMW l) (gateSV l) (gatePCPP l) s B hq0]
          exact hfitT
        erw [W3.NearCubicWires.RepairSource.Outer3.coreC_hardTable _ _ _ _ s z _ _ n h3 hcs htT]
        have hfun : ∀ (ν : ℕ) (e : ν = s)
            (hr' : ((gatePCPP l).output (W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l)
              (gatePCPP l) ν B)).clauseBits ≤ clauseWidth (recDG l) q)
            (ht' : recCopies (gateZeta_pos l) (gateZeta_lt l) q *
              ((W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l) (gatePCPP l) ν B).arity +
                clauseWidth (recDG l) q + 1) ≤ n),
            padCore (xorPower (paddedUnsigned ((gatePCPP l).output
              (W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l) (gatePCPP l) ν B)) hr')
              (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) ht' =
            padCore (xorPower (paddedUnsigned ((gatePCPP l).output
              (W3.NearCubicWires.RepairSource.Outer3.requestAt (gateMW l) (gateSV l) (gatePCPP l) s B)) hcs)
              (recCopies (gateZeta_pos l) (gateZeta_lt l) q)) htT := by
          intro ν e hr' ht'
          subst e
          rfl
        rw [← hfun (Nat.log 2 (2 ^ s)) hlog hr hfit2]
        have hstrict : 1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (recCopies (gateZeta_pos l) (gateZeta_lt l) q) <
            1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q) := by linarith
        exact ⟨fun circuit hcap => (hsP circuit.eval ⟨circuit, hcap, rfl⟩).trans_lt hstrict,
          fun circuit hcap => (htP circuit.eval ⟨circuit, hcap, rfl⟩).trans_lt hstrict⟩
      · -- Hard oracle: `Ô*` has no `q^G`-gate circuit
        have hℓ : (NearCubicGates.Close.Outer.outC (gateMW l) (gateSV l) s
            (W3.NearCubicWires.RepairSource.Outer3.firstSrc (gateMW l) (gateSV l) (oracleDeg l) s z h1)).ell ≤ q :=
          NearCubicGates.Close.Outer.ell_le_width (gateMW l) (gateSV l) s _ (by omega) hs1
        have hno : ¬ _root_.NearCubicWires.RepairSource.RecoveryChoice.SmallOracle
            (W3.NearCubicWires.RepairSource.Outer3.matchPCP (gateMW l) (gateSV l) s hℓ
              (W3.NearCubicWires.RepairSource.Outer3.firstOracle (gateMW l) (gateSV l) (oracleDeg l) s z h1 h2))
            (oracleDeg l) z :=
          fun h => h3 ⟨h1, h2, hℓ, h⟩
        erw [W3.NearCubicWires.RepairSource.Outer3.coreC_hardOracle _ _ _ _ s z _ _ n h1 h2 h3]
        exact caseOne _ (W3.NearCubicWires.RepairSource.Outer3.pfFn_hard (gateMW l) (gateSV l) (oracleDeg l) s z hℓ _ hno)
    · -- the exceptional length does not occur: the short PCP's completeness gives an accepted outer oracle
      exfalso
      have hbsize : (W3.NearCubicWires.RepairSource.Outer3.firstSrc (gateMW l) (gateSV l) (oracleDeg l) s z h1).size ≤
          RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) q :=
        (_root_.NearCubicWires.RepairSource.RecoveryChoice.oracleSelector
          (W3.NearCubicWires.RepairSource.Outer3.checkPCP (gateMW l) (gateSV l) s z) (oracleDeg l) z h1).sizeBounded
      have hcheck : NearCubicGates.Close.Outer.Check s z
          (W3.NearCubicWires.RepairSource.Outer3.firstSrc (gateMW l) (gateSV l) (oracleDeg l) s z h1) :=
        (NearCubicGates.Close.ENP.unitOuter_check s _ _ z z _ (fun _ => false)).mp
          ((_root_.NearCubicWires.RepairSource.RecoveryChoice.oracleSelector
            (W3.NearCubicWires.RepairSource.Outer3.checkPCP (gateMW l) (gateSV l) s z) (oracleDeg l) z h1).accepts
            (fun _ => false))
      have hfits := hfit₀ s (by omega) _ hbsize
      obtain ⟨O, hO⟩ := NearCubicGates.Close.Outer.honest (gateMW l) (gateSV l) s z
        (W3.NearCubicWires.RepairSource.Outer3.firstSrc (gateMW l) (gateSV l) (oracleDeg l) s z h1) (by omega) hs1
        hsq.le hfits hcheck hyes
      exact h2 (NearCubicGates.Close.Transfer.honestTable_of_oracle _ O hO)
  · -- Hard word: `X_z` has no `q^G`-gate circuit
    erw [W3.NearCubicWires.RepairSource.Outer3.coreC_hardWord _ _ _ _ s z _ _ n h1]
    exact caseOne _ (W3.NearCubicWires.RepairSource.Outer3.srcFn_hard (gateMW l) (gateSV l) (oracleDeg l) s z h1)

include hG in
/-- **The recovered language is hard in both classes** at row B's exponents, at every positive multiplier (Theorem 1.1,
row B: `c = 1/8`, `K_T = 11/2`, `K_S = 9/2`). -/
theorem recLanguageCut2_hardOk (cutoff : ℕ) :
    (∀ AT : ℝ, 0 < AT → ThrHardAt (1 / 8) (11 / 2) (recLanguageCut2 l (recMachine2Ok l G U P) cutoff) AT) ∧
    (∀ AS : ℝ, 0 < AS → SymHardAt (1 / 8) (9 / 2) (recLanguageCut2 l (recMachine2Ok l G U P) cutoff) AS) := by
  have hq := tendsto_sliceWidth l
  have hrange : ∀ᶠ n : ℕ in atTop, sliceWidth l n ≤ n ∧
      n ≤ (6 * ((recSched l).J + 1) + 2) * sliceWidth l n * (Nat.log 2 (Lq (sliceWidth l n)) + 1) := by
    filter_upwards [(recSched l).eventually_lengths] with n h
    exact ⟨h.2.2.1, h.2.2.2⟩
  have hlang : ∀ᶠ n : ℕ in atTop, recLanguageCut2 l (recMachine2Ok l G U P) cutoff n =
      recLanguage2 l (recMachine2Ok l G U P) n := by
    filter_upwards [(tendsto_two_pow_sourceIdx (recSched l)).eventually (eventually_ge_atTop cutoff)] with n h
    rw [recLanguageCut2_eq, if_pos h]
  have hsl := eventually_slice3Ok l G hG U P
  refine ⟨?_, ?_⟩
  · exact rowB_thrHardAt G.row.cap hG.aT (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) _ _
      (sliceWidth l) hq hrange
      (fun n => xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (sliceWidth l n)))
      (by
        filter_upwards [hsl, hlang] with n h hl
        intro circuit hwire
        rw [hl]
        exact h.2 circuit (Nat.le_floor hwire))
      (Eventually.of_forall fun _ => le_rfl)
  · exact rowB_symHardAt G.row.cap hG.aS (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) _ _
      (sliceWidth l) hq hrange
      (fun n => xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (sliceWidth l n)))
      (by
        filter_upwards [hsl, hlang] with n h hl
        intro circuit hwire
        rw [hl]
        exact h.1 circuit (Nat.le_floor hwire))
      (Eventually.of_forall fun _ => le_rfl)

end Leaf3

/-- **The recovery leaf at the live setup** (at the clock `kclk`): for every union leaf with the atom test and
every primitive, the recovered language (with the cutoff of its `E^NP` certificate), the certificate, and both hardness
statements. The certificate is the one input (`Split.CertGen`, §H.6). -/
noncomputable def recoveryLeaf2Ok (l : Literals) (G : Split.Gate) (hG : GateRel l G) (cert : Split.CertGen l) :
    Split.RecoveryLeaf2 G (unionSetupS2 l G) := fun _ _ _ _ U P =>
  { language := fun _ => recLanguageCut2 l (recMachine2Ok l G U P)
      (Classical.choose (cert _ (U.toUnionConstruction.runtime3 P (recL l kclk)).littleO))
    certificate := fun _ => Classical.choice
      (Classical.choose_spec (cert _ (U.toUnionConstruction.runtime3 P (recL l kclk)).littleO))
    thr := fun _ _ _ => (recLanguageCut2_hardOk l G hG U P _).1
    sym := fun _ _ _ => (recLanguageCut2_hardOk l G hG U P _).2 }

end NearCubicWires.WireExponent3_5.Transfer

end

