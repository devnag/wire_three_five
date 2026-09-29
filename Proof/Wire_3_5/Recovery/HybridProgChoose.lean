import Proof.Wire_3_5.Recovery.HybridProgBudget

/-! # The hybrid `E^NP` program: choosing its constants (P3:3738-3741, 3758-3759; D1.6 D)

Realizes the choice behind "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on the source
length `N_{a(n)}`" (P3:3758-3759) with "Choose the largest `a` such that `m_a ≤ n/2`" (P3:3738-3740): from the literal
set, the gate, the clock exponent and a weak machine within `o(T(N))`, one parameter set of the hybrid program and
its suppliers. The onset is chosen once and above every threshold: the prefix's scan index equals the paper's
`a(n)` (`prefix_index`), the native width lies below the padded width (`recSetup2_width`), `t(q)+1` exceeds
the amplifier's arity coefficient (the schedule's `t_tendsto`), and Case 2's cutoff (`two_runs`). Case 1's fits
at a live length then follow from `m_{a(n)} ≤ n/2`. The recovery capacities and budgets are base's, as in base's
`CommonProgramChoose`.

Paper quantity of the main type (`choose`): the hybrid program's parameters and suppliers at `(l, G, kclk, M)`. -/

set_option autoImplicit false

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage OrdinaryOracleCompose
open ProjectionNormalization SelectedRecoveryIntegration RecoveryScheduleEnvelope
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.WireExponent3_5.Ledger
noncomputable section

/-- **Case 1's fits at a live length** from `m_{a(n)} ≤ n/2`. -/
theorem case_one_fits (p : Parameters) (n₀ N₀ q₁ : ℕ) (hApad : (gateSource p.l).degrees.proofLog + 6 ≤ p.G.Apad)
    (hn₀ : ∀ n, n₀ ≤ n → index p n = sliceIdx (gateZeta_pos p.l) (gateZeta_lt p.l) p.kclk p.G.Apad (recDG p.l) n)
    (hN₀ : ∀ N, N₀ ≤ N → (recSetup2 p.l p.G p.kclk 0 0 0 (Nat.zero_le _)).pcp.nativeWidth N =
      Ledger.nativeWidth p.kclk p.G.Apad N)
    (hq₁ : ∀ q, q₁ ≤ q → (selectedAmplifier p.sources.amplification p.degree).arityCoefficient ≤
      rowBt (gateZeta_pos p.l) (gateZeta_lt p.l) q + 1)
    (hcut : max (2 ^ n₀) (max N₀ (max 2 (2 ^ q₁))) ≤ p.onset) : CaseOneFits p := by
  intro n x hlive
  have h0 := gateZeta_pos p.l
  have h1 := gateZeta_lt p.l
  have hSn : index p n ≤ n := CertPrefix.prefixS_le _ _ _ _ _ n
  have hc1 : 2 ^ n₀ ≤ 2 ^ index p n := (le_max_left _ _).trans (hcut.trans hlive)
  have hc2 : N₀ ≤ 2 ^ index p n := ((le_max_left _ _).trans (le_max_right _ _)).trans (hcut.trans hlive)
  have hc3 : 2 ≤ 2 ^ index p n :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hcut.trans hlive)
  have hc4 : 2 ^ q₁ ≤ 2 ^ index p n :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans (hcut.trans hlive)
  have hn₀S : n₀ ≤ index p n := (Nat.pow_le_pow_iff_right (by norm_num)).1 hc1
  have hq₁S : q₁ ≤ index p n := (Nat.pow_le_pow_iff_right (by norm_num)).1 hc4
  have hS1 : index p n ≠ 0 := by
    intro h; rw [h] at hc3; norm_num at hc3
  have hslice := hn₀ n (hn₀S.trans hSn)
  -- the schedule's fit `m_{a(n)} ≤ n/2`
  have hcore : coreLen h0 h1 p.kclk p.G.Apad (recDG p.l) (index p n) ≤ n / 2 := by
    rw [coreLen_eq]
    have he : Nat.findGreatest (fun a => (recSchedule h0 h1 p.kclk p.G.Apad (recDG p.l)).coreLength a ≤ n / 2) n =
        index p n := by
      rw [hslice, sliceIdx_eq]; rfl
    exact Nat.findGreatest_of_ne_zero
      (P := fun a => (recSchedule h0 h1 p.kclk p.G.Apad (recDG p.l)).coreLength a ≤ n / 2) he hS1
  -- the native width below the padded width
  have hRq : R p ⟨2 ^ index p n, x⟩ ≤ qAt p n := by
    have e := hN₀ (2 ^ index p n) hc2
    change max ((recPCP p.l p.kclk).pcp.nativeWidth (2 ^ index p n))
      (Ledger.nativeWidth p.kclk p.G.Apad (2 ^ index p n)) = _ at e
    change (recPCP p.l p.kclk).pcp.nativeWidth (2 ^ index p n) ≤ Transfer.widthAt p.kclk p.G.Apad (index p n)
    rw [widthAt_eq, ← e]
    exact le_max_left _ _
  have hSq : index p n ≤ qAt p n := by
    change index p n ≤ Transfer.widthAt p.kclk p.G.Apad (index p n)
    unfold Transfer.widthAt
    have := Nat.le_mul_of_pos_right (index p n) (show 0 < p.kclk + 2 by omega)
    omega
  have hq : qAt p n + 1 ≤ addrWidth (recDG p.l) (qAt p n) := by unfold addrWidth; omega
  have hcore' : (sched (gateCParams1 p.l).ζ h0 h1 (Lq (qAt p n)) + 1) * addrWidth (recDG p.l) (qAt p n) ≤ n / 2 :=
    hcore
  have haw : addrWidth (recDG p.l) (qAt p n) ≤ n / 2 :=
    (Nat.le_mul_of_pos_left _ (by omega)).trans hcore'
  have hR1 : 1 ≤ R p ⟨2 ^ index p n, x⟩ := by
    exact le_trans (Nat.succ_pos _) (native_lower p.l p.kclk (index p n))
  have harity := CloseoutParameters.arity_envelope (selectedAmplifier p.sources.amplification p.degree)
    (selectedAmplifier p.sources.amplification p.degree).arityCoefficient (R p ⟨2 ^ index p n, x⟩) 0 le_rfl hR1
    (RecoveryCaseOneRequest.request (globalPCP p) x).function
  have hcop := hq₁ (qAt p n) (hq₁S.trans hSq)
  have hmul : (selectedAmplifier p.sources.amplification p.degree).arityCoefficient * (R p ⟨2 ^ index p n, x⟩ + 0 + 1) ≤
      (sched (gateCParams1 p.l).ζ h0 h1 (Lq (qAt p n)) + 1) * addrWidth (recDG p.l) (qAt p n) :=
    Nat.mul_le_mul hcop (by omega)
  refine ⟨by omega, Nat.pow_le_pow_right (by norm_num) hSn, by omega, ?_⟩
  exact harity.trans (hmul.trans (hcore'.trans (Nat.div_le_self n 2)))

/-- **The hybrid program's constants and suppliers** at a literal set, a gate, a clock and a weak machine within
`o(T(N))`; its scan index equals the paper's `a(n)` past `n₀` with `2^{n₀} ≤ onset`. -/
theorem choose (l : Literals) (G : Split.Gate) (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) (kclk : ℕ)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n ^ (kclk + 2))) :
    ∃ (e1 e2 e3 f1 f2 f3 f4 onset Aw Bw Aq Bq : ℕ) (refuter : OrdinaryOracleProgram) (c : Constants),
      (∃ n₀, 2 ^ n₀ ≤ onset ∧ ∀ n, n₀ ≤ n →
        CertPrefix.prefixS kclk G.Apad (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) (recDG l) n =
          sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n) ∧
      Suppliers ⟨l, G, kclk, 0, e1, e2, e3, f1, f2, f3, f4, onset, Aw, Bw, Aq, Bq, refuter⟩ M c := by
  have h0 := gateZeta_pos l
  have h1 := gateZeta_lt l
  have hD : 1 ≤ recDG l := by unfold recDG; omega
  let clock : OrdinaryClock (fun n => n ^ (kclk + 2)) := PolynomialClock.ordinaryClock kclk
  let src := fixedProjection l.eightSources
  let H := (l.eightSources.hierarchy (fun n => n ^ (kclk + 2)) clock).hierarchy
  let Cpad := padding l.eightSources kclk clock
  have hc : H.coefficient ≤ Cpad := Nat.le_max_left _ _
  have hp : kclk + 3 ≤ Cpad := Nat.le_max_right _ _
  obtain ⟨Aw, Bw, capacity⟩ :=
    CloseoutRecoveryCapacity.actual_capacity_with_source src H Cpad (recOracleDeg l) hc hp
  obtain ⟨recoveryC, recoveryE, _recoveryPositive, recoveryBound⟩ :=
    RecoveryBoundedCold.polynomial_budget src H Cpad (recOracleDeg l) hc hp
  obtain ⟨f1, f2, f3, f4, twoCut, twoC, twoE, htwo⟩ := CaseTwoRuns.two_runs l G kclk hApad
  obtain ⟨-, n₀, hn₀⟩ := CertPrefix.prefix_index kclk G.Apad (recDG l) h0 h1
  obtain ⟨N₀, hN₀⟩ := recSetup2_width l G kclk 0 0 0 (Nat.zero_le _) hApad
  obtain ⟨q₁, hq₁⟩ : ∃ q₁, ∀ q, q₁ ≤ q →
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)).arityCoefficient ≤ rowBt h0 h1 q + 1 := by
    have ht := (recSchedule h0 h1 kclk G.Apad (recDG l)).t_tendsto
    have hev := Filter.tendsto_atTop.1 ht
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)).arityCoefficient
    obtain ⟨q₁, hq⟩ := Filter.eventually_atTop.1 hev
    exact ⟨q₁, fun q h => hq q h⟩
  let cut := max (max (2 ^ n₀) (max N₀ (max 2 (2 ^ q₁)))) twoCut
  obtain ⟨e1, e2, e3, onset, honset, hcut, refuter, prefixC, prefixE, prefixRun⟩ :=
    WireExponent3_5.Cert.exists_selected_prefix l.eightSources kclk G.Apad (zu (gateCParams1 l).ζ)
      (zv (gateCParams1 l).ζ) (recDG l) cut Aw Bw clock hD (two_u_lt_v h0 h1) M hM
  obtain ⟨Aq, Bq, query⟩ := CloseoutCommonQueryClear.exists_capacity prefixC prefixE recoveryC recoveryE Aw Bw
  let p : Parameters := ⟨l, G, kclk, 0, e1, e2, e3, f1, f2, f3, f4, onset, Aw, Bw, Aq, Bq, refuter⟩
  let c : Constants := ⟨prefixC, prefixE, recoveryC, recoveryE, twoC, twoE⟩
  have hcut1 : max (2 ^ n₀) (max N₀ (max 2 (2 ^ q₁))) ≤ onset := (le_max_left _ _).trans hcut
  have hcut2 : twoCut ≤ onset := (le_max_right _ _).trans hcut
  refine ⟨e1, e2, e3, f1, f2, f3, f4, onset, Aw, Bw, Aq, Bq, refuter, c,
    ⟨n₀, (le_max_left _ _).trans hcut1, hn₀⟩, ?_⟩
  change Suppliers p M c
  refine ⟨honset, ?_, ?_, case_one_fits p n₀ N₀ q₁ hApad hn₀ hN₀ hq₁ hcut1, ?_, ?_, query⟩
  · intro bits
    obtain ⟨fuel, hfuel, out, actual, address, flag, rawCapacity, word, liveFields⟩ := prefixRun bits
    refine ⟨fuel, hfuel, out, actual, address, congrArg (fun w => readTapeBit w 0) flag, ?_⟩
    intro live
    obtain ⟨_conflict, padding, hpadding, rawQuery⟩ := liveFields live
    have hresult : (if onset ≤ length p bits.length then
        List.ofFn ((l.eightSources.hierarchy (fun n => n ^ (kclk + 2)) clock).output M (length p bits.length)) else []) =
        List.ofFn (selectedWord p M bits.length) := by
      rw [if_pos live]
      rfl
    change out (prefixRecoveryFields p 0) =
      frame (if onset ≤ length p bits.length then
        List.ofFn ((l.eightSources.hierarchy (fun n => n ^ (kclk + 2)) clock).output M (length p bits.length)) else []) ++
      frame (H.time (if onset ≤ length p bits.length then
        List.ofFn ((l.eightSources.hierarchy (fun n => n ^ (kclk + 2)) clock).output M (length p bits.length))
          else []).length).bits at word
    rw [hresult, List.length_ofFn] at word
    refine ⟨padding, hpadding, ?_⟩
    intro j
    fin_cases j
    · exact word
    · exact rawCapacity
    · exact rawQuery
  · intro n point x hN small
    obtain ⟨answer, actual, value⟩ := htwo n point x (hcut2.trans hN) small
    refine ⟨answer, ?_, value⟩
    have hd := recovery_description p ⟨2 ^ index p n, x⟩ small
    rw [hd]
    exact actual
  · intro n r hn hr
    obtain ⟨hN, hW, _hR, _hQ, _hB, hbytes, htwo'⟩ := capacity n r hn hr
    exact ⟨hN, hW, hbytes, htwo'⟩
  · intro r W fits
    have hR := native_width p r
    have hQ := native_queries p r
    have hP := native_source p r
    change PCPPNativeHierarchyNodes.width src kclk H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 = R p r at hR
    change PCPPNativeHierarchyNodes.queries src kclk H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 = Q p r at hQ
    change PCPPNativeHierarchyNodes.pcp src kclk H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 =
      sourcePCP p r at hP
    apply recoveryBound r W fits.length
    · rw [hR, hQ, hP]
      exact fits.workspace
    · rw [hR]
      exact fits.two

end

end NearCubicWires.RepairSource.HybridProgram
