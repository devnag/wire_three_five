import Proof.Wire_3_5.Recovery.CaseTwoReceipt
import Proof.Wire_3_5.Recovery.HybridLeaf

/-! # The hybrid slice's Case-2 bit is computed in `2^{O(n)}` (P3:3728-3729, 3763-3771; D1.6 A4)

Realizes, for the hybrid recovered language (`recLanguage2`), "In the yes case, prefix self-reduction recovers the
first eligible description, after which each honest proof bit is computed by the deterministic PCPP algorithm"
(P3:3763-3765), for the XOR power of "Lemma tr:xor makes `f^{⊕t(q)}` correlation hard" (P3:3728-3729; the formal
schedule's copy count is `t(q)+1`, `recLanguage2`), within "`2^{O(n)}` overall" (P3:3769-3771):

**`two_runs`** (the hybrid program's `TwoRuns`, in the shape of base's `CloseoutCaseTwo.Selected.selected_polynomial_run`):
for fixed capacity exponents, a cutoff and `C, E`, at every address length `n` with source index `S = prefixS … n`
(the prefix, `= a(n)` past its onset) and every small-oracle source word `x` at `2^S` above the cutoff, the hybrid
machine `CaseTwoExec.htwo` runs from the five cold words (the refuter hierarchy's word at `⟨2^S, x⟩`, the recovered
description, the framed address, `1^R`, `1^B`) within `C·(2^n+1)^E` steps and writes the framed bit
`hybridCore … x (t(q)+1) ⌈d_G log₂(q+2)⌉ n point` at `q = q(2^S)` — the hybrid slice's Case-2 bit (`hybridCore_two`).

The identification: the padded request of the union setup at the cast oracle is the cast of the native substituted
request (`unionRequest_pad`, base's compaction idempotence), the padded width is `q(2^S)` past a cutoff
(`recSetup2_width`), the clause bits fit `⌈d_G log₂(q+2)⌉` (the PCPP's clause count, `requestSize2_le`), the schedule
counter is `t(q)` (`roundCount_sched`) and the `t(q)+1` blocks fit in `n/2` (the slice's `coreLength_sourceIdx`).

Paper quantity of the main type (`two_runs`): the hybrid slice's Case-2 bit `hybridCore … n point`, in `C·(2^n+1)^E`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoRuns
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleSizeBound_monotone)
open NearCubicWires.RecoveryPipeline (padCore)
open NearCubicWires.RepairSource.CloseoutLanguage (paddedUnsigned clauseWidth)
open NearCubicWires.RepairSource.RecoveryChoice (SmallOracle oracleSelector)
open NearCubicWires.ProjectionPCPPadding (padProjectionPCP)
open NearCubicWires.OuterPCPRecovery NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec NearCubicWires.WireExponent3_5.Transfer.CaseTwoReceipt

noncomputable section

section Sched
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The schedule counter is `t(q)`** once `t(q) ≤ c + 1` (the candidate's round count, as in `scanFlag_eq`). -/
theorem candT_sched (k A a c : ℕ) (hc : sched ζ h0 h1 (Lq (widthAt k A a)) ≤ c + 1) :
    candT k A (zu ζ) (zv ζ) a ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) c = sched ζ h0 h1 (Lq (widthAt k A a)) := by
  unfold candT
  have e1 : candA0 k A (zu ζ) (zv ζ) a = schedA ζ (Lq (widthAt k A a)) 0 := by
    unfold candA0 candL0 schedA; ring
  have e2 : candB0 (zv ζ) = schedB ζ 0 := by unfold candB0 schedB; ring
  rw [e1, e2, roundCount_sched h0 h1 _ c hc]

end Sched

section Runs
variable (l : Literals) (G : Split.Gate) (kclk : ℕ)

section Oracle
variable {S : ℕ} (x : BitInput (2 ^ S)) (small : SmallOracle (recPCP l kclk).pcp (recOracleDeg l) x)

/-- The padded request of the union setup at the cast recovered oracle. -/
abbrev reqU : PCPPRequest (gatePCPP l).minimumArity :=
  unionRequest (padProjectionPCP (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _))
    (gatePCPP l) x (castCircuit (le_max_left _ _) (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) x small).circuit)

/-- **The padded request's clause bits fit `⌈d_G log₂(q+2)⌉`** at `q = q(2^S)` above the clause-count threshold. -/
theorem reqU_clause (hqS : paddedWidth l G (refH l kclk) (2 ^ S) = widthAt kclk G.Apad S)
    (hK : (gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree ≤ widthAt kclk G.Apad S + 2) :
    ((gatePCPP l).output (reqU l G kclk x small)).clauseBits ≤ clauseWidth (recDG l) (widthAt kclk G.Apad S) := by
  have hwN : (recPCP l kclk).pcp.nativeWidth (2 ^ S) ≤ paddedWidth l G (refH l kclk) (2 ^ S) := le_max_left _ _
  have hsizeO : (castCircuit hwN (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) x small).circuit).size ≤
      oracleSizeBound (recOracleDeg l) ((recSetup2 l G kclk 0 0 0 (Nat.zero_le _)).pcp.nativeWidth (2 ^ S)) := by
    rw [castCircuit_size]
    exact (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) x small).sizeBounded.trans
      (oracleSizeBound_monotone _ hwN)
  have hqS' : (recSetup2 l G kclk 0 0 0 (Nat.zero_le _)).pcp.nativeWidth (2 ^ S) = widthAt kclk G.Apad S := hqS
  have hsize : (reqU l G kclk x small).circuit.size + 1 ≤ recKs2 l kclk * (widthAt kclk G.Apad S + 1) ^ recSigma l :=
    (requestSize2_le l G kclk 0 0 0 (Nat.zero_le _) x _ hsizeO).trans (le_of_eq (by rw [hqS']))
  have hcc := (gatePCPP l).clauseCountBound (reqU l G kclk x small)
  apply clauseBits_le
  calc _ ≤ _ := hcc
    _ ≤ (gatePCPP l).coefficient * (recKs2 l kclk * (widthAt kclk G.Apad S + 1) ^ recSigma l) ^
          (gatePCPP l).degree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize _)
    _ = ((gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree) *
          (widthAt kclk G.Apad S + 1) ^ (recSigma l * (gatePCPP l).degree) := by
        rw [mul_pow, ← pow_mul]; ring
    _ ≤ (widthAt kclk G.Apad S + 2) * (widthAt kclk G.Apad S + 2) ^ (recSigma l * (gatePCPP l).degree) :=
        Nat.mul_le_mul hK (Nat.pow_le_pow_left (by omega) _)
    _ = (widthAt kclk G.Apad S + 2) ^ recDG l := by unfold recDG; ring

/-- The padded request's arity is `q(2^S)`. -/
theorem reqU_arity (hqS : paddedWidth l G (refH l kclk) (2 ^ S) = widthAt kclk G.Apad S)
    (hmin : (gatePCPP l).minimumArity ≤ widthAt kclk G.Apad S) :
    (reqU l G kclk x small).arity = widthAt kclk G.Apad S :=
  (max_eq_left (show (gatePCPP l).minimumArity ≤ paddedWidth l G (refH l kclk) (2 ^ S) by rw [hqS]; exact hmin)).trans
    hqS

end Oracle

/-- **The hybrid Case-2 bit at one live length**: given the selected-PCP run (`HSelRun`) and the live side conditions
at `S` (the padded width is `q(2^S)`, `q` exceeds the PCPP's minimum arity and its clause-count threshold,
`t(q) ≤ n + 1`, and the core fits in `n/2`), the hybrid machine writes the slice's Case-2 bit within `C·(2^n+1)^E`. -/
theorem run_at (e1 e2 e3 e4 C E : ℕ)
    (hsel : HSelRun (gateSource l) (gatePCPP l) (refH l kclk) (cpadOf (refH l kclk)) (le_max_right _ _) G.Apad
      (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) e1 e2 e3 e4 (recOracleDeg l) (recDG l) C E)
    (n S : ℕ) (hS : CertPrefix.prefixS kclk G.Apad (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) (recDG l) n = S)
    (point : BitInput n) (x : BitInput (2 ^ S)) (small : SmallOracle (recPCP l kclk).pcp (recOracleDeg l) x)
    (hSn : S ≤ n) (hqS : paddedWidth l G (refH l kclk) (2 ^ S) = widthAt kclk G.Apad S)
    (hmin : (gatePCPP l).minimumArity ≤ widthAt kclk G.Apad S)
    (hK : (gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree ≤ widthAt kclk G.Apad S + 2)
    (hsched : sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) (Lq (widthAt kclk G.Apad S)) ≤ n + 1)
    (hcore : coreLen (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) S ≤ n / 2) :
    ∃ out, ClockJoin.ReadyRun (htwo (gateSource l) (gatePCPP l) kclk (recDG l) G.Apad (zu (gateCParams1 l).ζ)
        (zv (gateCParams1 l).ζ) e1 e2 e3 e4 (refH l kclk).coefficient (cpadOf (refH l kclk))
        (VerifierEncoding.code (refH l kclk).verifier)) (C * (2 ^ n + 1) ^ E)
      (htwoIn (gateSource l) (gatePCPP l) kclk (recDG l) (HierarchySourceInput.hierarchyInput (refH l kclk) ⟨2 ^ S, x⟩)
        (RepairOrdinary.frame (recoveredPrefix
          (descriptionWidth ((recPCP l kclk).pcp.nativeWidth (2 ^ S))
            (oracleSizeBound (recOracleDeg l) ((recPCP l kclk).pcp.nativeWidth (2 ^ S))))
          (boundedOracleRecoveryFormula (recPCP l kclk).pcp x
            (oracleSizeBound (recOracleDeg l) ((recPCP l kclk).pcp.nativeWidth (2 ^ S))))))
        (RepairOrdinary.frame (List.ofFn point)) ((recPCP l kclk).pcp.nativeWidth (2 ^ S))
        (oracleSizeBound (recOracleDeg l) ((recPCP l kclk).pcp.nativeWidth (2 ^ S)))) out ∧
      out (outSlot (gateSource l) (gatePCPP l) kclk (recDG l) 1) =
        RepairOrdinary.frame (hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _)
          (gatePCPP l) (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) x
          (sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) (Lq (widthAt kclk G.Apad S)) + 1)
          (clauseWidth (recDG l) (widthAt kclk G.Apad S)) n point).toNat.bits := by
  have hc := reqU_clause l G kclk x small hqS hK
  have ht : (sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) (Lq (widthAt kclk G.Apad S)) + 1) *
      ((reqU l G kclk x small).arity + clauseWidth (recDG l) (widthAt kclk G.Apad S) + 1) ≤ n := by
    rw [reqU_arity l G kclk x small hqS hmin]
    have h := hcore
    unfold coreLen addrWidth at h
    show _ * (widthAt kclk G.Apad S + Nat.clog 2 ((widthAt kclk G.Apad S + 2) ^ recDG l) + 1) ≤ n
    omega
  obtain ⟨out, hrun, hout⟩ := hsel (recPCP l kclk).pcp rfl S x
    (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) x small).circuit
    (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) x small).sizeBounded
    (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) point (by rw [hS]; exact hqS) (by rw [hqS]; exact hmin)
    hSn (clauseWidth (recDG l) (widthAt kclk G.Apad S))
    (sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) (Lq (widthAt kclk G.Apad S)) + 1)
    (by rw [hqS]) (by rw [hS, candT_sched (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad S n hsched]) hc ht
  refine ⟨out, ?_, ?_⟩
  · rw [CloseoutCaseTwo.Selected.recovered_description (recPCP l kclk).pcp (recOracleDeg l) x small]
    exact hrun
  · rw [hybridCore_two (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l)
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) x _ _ n small hc ht]
    exact hout

/-- The prefix's source index `S = prefixS … n` (`= a(n)` past the prefix's onset, `prefix_index`). -/
abbrev srcIdx (n : ℕ) : ℕ :=
  CertPrefix.prefixS kclk G.Apad (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) (recDG l) n

/-- The hybrid Case-2 machine at the capacity exponents `e₁…e₄`. -/
abbrev twoMachine (e1 e2 e3 e4 : ℕ) :=
  htwo (gateSource l) (gatePCPP l) kclk (recDG l) G.Apad (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) e1 e2 e3 e4
    (refH l kclk).coefficient (cpadOf (refH l kclk)) (VerifierEncoding.code (refH l kclk).verifier)

/-- The native width `R = R(2^S)` of the refuter hierarchy's outer PCP. -/
abbrev nativeR (S : ℕ) : ℕ := (recPCP l kclk).pcp.nativeWidth (2 ^ S)

/-- The oracle size bound `B = q^G` at `R(2^S)`. -/
abbrev oracleB (S : ℕ) : ℕ := oracleSizeBound (recOracleDeg l) (nativeR l kclk S)

/-- **The hybrid program's `TwoRuns`** (the shape of base's `CloseoutCaseTwo.Selected.selected_polynomial_run`): for
fixed capacity exponents, a cutoff and `C, E`, at every address length `n` with the prefix's source index
`S = prefixS … n` and every small-oracle source word `x` at `2^S ≥ cutoff`, the hybrid machine runs from the five cold
words (the hierarchy word at `⟨2^S, x⟩`, the recovered description, the framed address, `1^R`, `1^B`) within
`C·(2^n+1)^E` steps and writes the hybrid slice's Case-2 bit `hybridCore … x (t(q)+1) ⌈d_G log₂(q+2)⌉ n point`,
`q = q(2^S)`. -/
theorem two_runs (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∃ e1 e2 e3 e4 cutoff C E : ℕ, ∀ (n : ℕ) (point : BitInput n) (x : BitInput (2 ^ srcIdx l G kclk n)),
      cutoff ≤ 2 ^ srcIdx l G kclk n → SmallOracle (recPCP l kclk).pcp (recOracleDeg l) x →
      ∃ out, ClockJoin.ReadyRun (twoMachine l G kclk e1 e2 e3 e4) (C * (2 ^ n + 1) ^ E)
        (htwoIn (gateSource l) (gatePCPP l) kclk (recDG l)
          (HierarchySourceInput.hierarchyInput (refH l kclk) ⟨2 ^ srcIdx l G kclk n, x⟩)
          (RepairOrdinary.frame (recoveredPrefix
            (descriptionWidth (nativeR l kclk (srcIdx l G kclk n)) (oracleB l kclk (srcIdx l G kclk n)))
            (boundedOracleRecoveryFormula (recPCP l kclk).pcp x (oracleB l kclk (srcIdx l G kclk n)))))
          (RepairOrdinary.frame (List.ofFn point)) (nativeR l kclk (srcIdx l G kclk n))
          (oracleB l kclk (srcIdx l G kclk n))) out ∧
        out (outSlot (gateSource l) (gatePCPP l) kclk (recDG l) 1) =
          RepairOrdinary.frame (hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk))
            (fun _ => le_max_left _ _) (gatePCPP l) (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) x
            (sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l) (Lq (widthAt kclk G.Apad (srcIdx l G kclk n))) + 1)
            (clauseWidth (recDG l) (widthAt kclk G.Apad (srcIdx l G kclk n))) n point).toNat.bits := by
  have h0 := gateZeta_pos l
  have h1 := gateZeta_lt l
  have hD : 1 ≤ recDG l := by unfold recDG; omega
  obtain ⟨e1, e2, e3, e4, C, E, hsel⟩ := hselected_run (gateSource l) (gatePCPP l) (refH l kclk) (cpadOf (refH l kclk))
    (le_max_left _ _) (le_max_right _ _) hD G.Apad (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) (recOracleDeg l)
    (two_u_lt_v h0 h1)
  obtain ⟨-, n₀, hn₀⟩ := CertPrefix.prefix_index kclk G.Apad (recDG l) h0 h1
  obtain ⟨n₁, hn₁⟩ := eventually_sched_le h0 h1 kclk G.Apad
  obtain ⟨N₀, hN₀⟩ := recSetup2_width l G kclk 0 0 0 (Nat.zero_le _) hApad
  refine ⟨e1, e2, e3, e4, max (2 ^ (n₀ + n₁ + (2 * coreLen h0 h1 kclk G.Apad (recDG l) 0 + 2) +
    (gatePCPP l).minimumArity + (gatePCPP l).coefficient * recKs2 l kclk ^ (gatePCPP l).degree)) N₀, C, E,
    fun n point x hcut small => ?_⟩
  have hSn : srcIdx l G kclk n ≤ n :=
    CertPrefix.prefixS_le kclk G.Apad (zu (gateCParams1 l).ζ) (zv (gateCParams1 l).ζ) (recDG l) n
  have hslice : n₀ ≤ n → srcIdx l G kclk n = sliceIdx h0 h1 kclk G.Apad (recDG l) n := hn₀ n
  generalize hS : srcIdx l G kclk n = S at x hcut hSn hslice ⊢
  have hTS := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 ((le_max_left _ _).trans hcut)
  have hwS : S ≤ widthAt kclk G.Apad S := by
    unfold widthAt
    have := Nat.le_mul_of_pos_right S (show 0 < kclk + 2 by omega)
    omega
  have hqS : paddedWidth l G (refH l kclk) (2 ^ S) = widthAt kclk G.Apad S :=
    (hN₀ (2 ^ S) ((le_max_right _ _).trans hcut)).trans (widthAt_eq kclk G.Apad S).symm
  have hcore : coreLen h0 h1 kclk G.Apad (recDG l) S ≤ n / 2 := by
    rw [hslice (by omega), coreLen_eq, sliceIdx_eq]
    exact (recSchedule h0 h1 kclk G.Apad (recDG l)).coreLength_sourceIdx n (by rw [← coreLen_eq]; omega)
  exact run_at l G kclk e1 e2 e3 e4 C E hsel n S hS point x small hSn hqS (by omega) (by omega)
    (hn₁ n (by omega) S hSn) hcore

end Runs

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoRuns
