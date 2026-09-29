import Proof.Wire_3_5.Recovery.HybridLeaf
import Proof.Wire_3_5.Recovery.HybridLedgerOk
import Proof.Wire_3_5.Recovery.HybridAssemblyOk

/-! # The recovery leaf at `S₂` for union leaves with the atom test

"Lemma tr:completeness would then supply an accepting sparse guess in that mode, contradicting rejection of the union
machine. The same `f` is therefore approximate-sum hard in both modes" (P3:3711-3729), at the constructed guess, which
passes the atom test (P3:3670). For `U : UnionLeafAt2`: `eventually_slice2Ok` (every large slice of the hybrid language is
hard in both classes), `recLanguageCut2_hardOk` (row B's hardness), **`recoveryLeaf2Ok`** (`Split.RecoveryLeaf2` from
D1.6's certificate). The hybrid language (`recLanguage2`, `recLanguageCut2`) is the unchanged one.

Paper quantity of the main type: the recovery leaf (the hybrid recovered language, its certificate, both hardnesses). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open Filter

section Leaf2Ok
variable (l : Literals) (G : Split.Gate) (hG : GateRel l G) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
  (U : Split.UnionLeafAt2 (G.inputs kclk coef A a ha) (unionSetupS2 l G kclk coef A a ha))
  (P : FusedPrimitive (G.inputs kclk coef A a ha))

include hG in
/-- **Every large slice of the hybrid language is hard in both classes** within the integer per-atom caps. -/
theorem eventually_slice2Ok :
    ∀ᶠ n : ℕ in atTop,
      (∀ circuit : SymmetricThresholdCircuit n,
        circuit.wireCount ≤ ⌊wireCap G.row.cap .sym (recWidth l G kclk n)⌋₊ →
        agreement circuit.eval (recLanguage2 l G kclk (recMachine2Ok l G U P) n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n))) ∧
      (∀ circuit : ThresholdThresholdCircuit n,
        circuit.wireCount ≤ ⌊wireCap G.row.cap .thr (recWidth l G kclk n)⌋₊ →
        agreement circuit.eval (recLanguage2 l G kclk (recMachine2Ok l G U P) n) <
          1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n))) := by
  have hc := l.eightSources.amplification.stvExponentPositive
  have hs := (recSched l G kclk).tendsto_sourceIdx
  have hN := tendsto_two_pow_sourceIdx (recSched l G kclk)
  have hq := tendsto_recWidth l G kclk
  obtain ⟨onR, hR⟩ := rejected_yes_eventually2Ok l G U P
  obtain ⟨onC, hC⟩ := complete2Ok l G U P
  obtain ⟨cB, dB, _, hB⟩ := recBudget2_poly l kclk
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (eventually_big (3 * widthK kclk G.Apad ^ 4 + 1))
  have hNev : ∀ᶠ N : ℕ in atTop,
      ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N = nativeWidth kclk G.Apad N ∧
        ∀ (z : BitInput N) (oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N)),
          ((recSetup2 l G kclk coef A a ha).request z oracle).arity = nativeWidth kclk G.Apad N) ∧
      onR ≤ N ∧ onC ≤ N ∧ (G.budget kclk coef A a ha).onset ≤ N ∧
      cB * (nativeWidth kclk G.Apad N + 1) ^ dB ≤ N / 16 := by
    filter_upwards [eventually_request_arity2 l G kclk coef A a ha hG.apad, eventually_ge_atTop onR,
      eventually_ge_atTop onC, eventually_ge_atTop (G.budget kclk coef A a ha).onset,
      eventually_poly_le_div16 kclk G.Apad cB dB] with N h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hK : ∀ᶠ q : ℕ in atTop, (gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree ≤ q + 2 ∧
      6 * ((recSched l G kclk).J + 1) + 2 ≤ q := by
    filter_upwards [eventually_ge_atTop ((gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree +
      (6 * ((recSched l G kclk).J + 1) + 2))] with q hq
    exact ⟨by omega, by omega⟩
  filter_upwards [hN.eventually hNev, hq.eventually (eventually_recQ l G hG), hq.eventually hK,
    (recSched l G kclk).eventually_lengths, hs.eventually (eventually_ge_atTop R₀),
    hq.eventually (eventually_caseOne_advR (gateZeta_pos l) (gateZeta_lt l) _ hc (widthK kclk G.Apad))]
    with n hNn hQn hKn hlen hsR hadv
  obtain ⟨⟨hw, harity⟩, hRn, hCn, hBn, hbud⟩ := hNn
  obtain ⟨-, hlen2, -, hnq⟩ := hlen
  -- the native width `R` at `2^{a(n)}`
  have hlow := native_lower l kclk ((recSched l G kclk).sourceIdx n)
  have hRq : (recPCP l kclk).pcp.nativeWidth (2 ^ (recSched l G kclk).sourceIdx n) ≤ recWidth l G kclk n := by
    have h1 : (recPCP l kclk).pcp.nativeWidth (2 ^ (recSched l G kclk).sourceIdx n) ≤
        (recSetup2 l G kclk coef A a ha).pcp.nativeWidth (2 ^ (recSched l G kclk).sourceIdx n) := le_max_left _ _
    rw [hw] at h1
    exact h1
  have hqR : recWidth l G kclk n ≤ widthK kclk G.Apad * (recPCP l kclk).pcp.nativeWidth (2 ^ (recSched l G kclk).sourceIdx n) := by
    have h1 := widthAt_le kclk G.Apad ((recSched l G kclk).sourceIdx n)
    rw [widthAt_eq] at h1
    exact h1.trans (Nat.mul_le_mul_left _ hlow)
  exact core_hard_at2_ok l G hG P (recMachine2Ok l G U P) _ (recWidth l G kclk n) n
    ((recPCP l kclk).pcp.nativeWidth (2 ^ (recSched l G kclk).sourceIdx n)) hw (harity _)
    (hR _ hRn).1 (hR _ hRn).2 (fun g hg hok => hC _ hCn _ g hg hok) ((G.budget kclk coef A a ha).fits _ hBn)
    ((hB _).trans hbud) hQn hKn.1 (hlen2.trans (Nat.div_le_self _ _)) (n_succ_le _ _ n hKn.2 hnq) rfl
    (by omega) hRq hqR (hR₀ _ (by omega)) (hadv _ (by omega) hqR)

include hG in
/-- **The hybrid recovered language is hard in both classes** at row B's exponents, at every positive multiplier. -/
theorem recLanguageCut2_hardOk (cutoff : ℕ) :
    (∀ AT : ℝ, 0 < AT → ThrHardAt (1 / 8) (11 / 2) (recLanguageCut2 l G kclk (recMachine2Ok l G U P) cutoff) AT) ∧
    (∀ AS : ℝ, 0 < AS → SymHardAt (1 / 8) (9 / 2) (recLanguageCut2 l G kclk (recMachine2Ok l G U P) cutoff) AS) := by
  have hq := tendsto_recWidth l G kclk
  have hrange : ∀ᶠ n : ℕ in atTop, recWidth l G kclk n ≤ n ∧
      n ≤ (6 * ((recSched l G kclk).J + 1) + 2) * recWidth l G kclk n *
        (Nat.log 2 (Lq (recWidth l G kclk n)) + 1) := by
    filter_upwards [(recSched l G kclk).eventually_lengths] with n h
    exact ⟨h.2.2.1, h.2.2.2⟩
  have hlang : ∀ᶠ n : ℕ in atTop, recLanguageCut2 l G kclk (recMachine2Ok l G U P) cutoff n =
      recLanguage2 l G kclk (recMachine2Ok l G U P) n := by
    filter_upwards [(tendsto_two_pow_sourceIdx (recSched l G kclk)).eventually (eventually_ge_atTop cutoff)]
      with n h
    unfold recLanguageCut2
    rw [if_pos h]
  have hsl := eventually_slice2Ok l G hG U P
  refine ⟨?_, ?_⟩
  · exact rowB_thrHardAt G.row.cap hG.aT (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) _ _
      (recWidth l G kclk) hq hrange
      (fun n => xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n)))
      (by
        filter_upwards [hsl, hlang] with n h hl
        intro circuit hwire
        rw [hl]
        exact h.2 circuit (Nat.le_floor hwire))
      (Eventually.of_forall fun _ => le_rfl)
  · exact rowB_symHardAt G.row.cap hG.aS (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) _ _
      (recWidth l G kclk) hq hrange
      (fun n => xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n)))
      (by
        filter_upwards [hsl, hlang] with n h hl
        intro circuit hwire
        rw [hl]
        exact h.1 circuit (Nat.le_floor hwire))
      (Eventually.of_forall fun _ => le_rfl)

end Leaf2Ok

/-- **The recovery leaf at `S₂`**: for every union leaf with the atom test and every primitive, the hybrid recovered language, its certificate,
and both hardness statements. The certificate (D1.6's program) is the one input, for the language used here. -/
noncomputable def recoveryLeaf2Ok (l : Literals) (G : Split.Gate) (hG : GateRel l G)
    (cert2 : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
      (U : Split.UnionLeafAt2 (G.inputs kclk coef A a ha) (unionSetupS2 l G kclk coef A a ha))
      (P : FusedPrimitive (G.inputs kclk coef A a ha)),
      ∃ cutoff : ℕ, Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
        (recLanguageCut2 l G kclk (recMachine2Ok l G U P) cutoff))) :
    Split.RecoveryLeaf2 G (unionSetupS2 l G) := fun kclk coef A a ha U P =>
  { language := fun _ => recLanguageCut2 l G kclk (recMachine2Ok l G U P) (Classical.choose (cert2 kclk coef A a ha U P))
    certificate := fun _ => Classical.choice (Classical.choose_spec (cert2 kclk coef A a ha U P))
    thr := fun _ _ _ => (recLanguageCut2_hardOk l G hG U P _).1
    sym := fun _ _ _ => (recLanguageCut2_hardOk l G hG U P _).2 }

end NearCubicWires.WireExponent3_5.Transfer
