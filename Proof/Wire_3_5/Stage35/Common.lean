import Proof.Wire_3_5.Stage35.CommonRuns
import Proof.Wire_3_5.Stage35.AfterFinal
import Proof.Wire_3_5.Stage35.Lang
import Proof.CaseAnalysis.CloseoutRecoveryBudget

/-!
# The recovered language is in `E^NP`, from the Case-2 kit

Paper v2, §H.6 "Exact lengths and canonical recovery": "The resulting slice is computable in `E^NP`. Run the fixed
refuter to obtain `z`, and then make the case decision of §H.5 in three stages. Each stage is a SAT query of size
`2^{O(q)}` followed by prefix self-reduction […] There are at most `2^{O(q)}` SAT queries and local work, in addition to
`poly(T(N_a)) = 2^{O(q)}` refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall. Finite exceptional lengths may be
fixed arbitrarily." (stages in the near-cubic-wires order: source circuit, first accepted oracle `O*`, proof circuit
with `O_{B_pf} = O*`).

One ordinary SAT-oracle program on every input length: this proof's scan prefix (`Stage35.Cert`: the index `a(n)` of
the row-B schedule, the refuter's word `z` at `N = 2^{a(n)}`, the live flag `onset ≤ N`), then the after-prefix program
(`AfterRun`: the three stages, Case 1's amplifier on `X_z` or `Ô*`, the zero slice, or the Case-2 kit), or `false`.
`Closeout.certificate_of_runs` packages the runs into an ordinary `E^NP` certificate of `languageCut … onset`.

* `copies_large`: the copy count `t(q) + 1` eventually dominates the amplifier's arity coefficient;
* **`existsCertificate`**: from the Case-2 kit, for every cutoff and every weak machine within `o(T)`, an onset above the
  cutoff and an ordinary `E^NP` certificate of the recovered language `languageCut … M onset`.
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.Common

open Stage35 _root_.NearCubicGates.Close

open W3.Recovery3 NearCubicGates.Close.Recovery
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.RecoveryPipeline
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Ledger

variable {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ}

/-- A ready run of the recovery program is an ordinary oracle run. -/
theorem runs_of_ready (p : Params s P g) (bits : List Bool) (b : List Bool) (cost budget : ℕ)
    (out : Fin (tapes p) → List Bool)
    (h : Ready RecoveryOracle.correctedSat (program p) cost (input p bits) out)
    (ho : out (ports p).outputTape = RepairOrdinary.frame b) (hc : cost ≤ budget) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (program p) bits b budget := by
  obtain ⟨final, ht, hh, _, hf⟩ := h
  refine ⟨cost, final, hc, ?_, hh, ?_⟩
  · rw [ordinary_input]
    exact ht
  · change final.tapes (ports p).outputTape = _
    rw [hf]
    exact ho

theorem budget_le (C E Ca Ea n : ℕ) (a b : ℕ) (ha : a ≤ C * (2 ^ n + 1) ^ E) (hb : b ≤ Ca * (2 ^ n + 1) ^ Ea) :
    a + 1 + (b + 1) ≤ (C + Ca + 8) * (2 ^ n + 1) ^ (E + Ea) := by
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have h1 : (2 ^ n + 1) ^ E ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.pow_le_pow_right hx (Nat.le_add_right E Ea)
  have h2 : (2 ^ n + 1) ^ Ea ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.pow_le_pow_right hx (Nat.le_add_left Ea E)
  have h3 : 1 ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.one_le_pow _ _ hx
  have ha' := ha.trans (Nat.mul_le_mul_left C h1)
  have hb' := hb.trans (Nat.mul_le_mul_left Ca h2)
  nlinarith

theorem small_le (C E Ca Ea n c : ℕ) (hc : c ≤ C * (2 ^ n + 1) ^ E) :
    c + 6 ≤ (C + Ca + 8) * (2 ^ n + 1) ^ (E + Ea) := by
  have h2 : 1 ≤ (2 ^ n + 1) ^ (E + Ea) := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
  have h3 : (2 ^ n + 1) ^ E ≤ (2 ^ n + 1) ^ (E + Ea) :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
  have h4 := Nat.mul_le_mul_left C h3
  nlinarith

section
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The copy count `t(q) + 1` is positive. -/
theorem copies_pos (q : ℕ) : 1 ≤ copies h0 h1 q := by
  show 1 ≤ rowBt h0 h1 q + 1
  omega

/-- **The copy count eventually dominates any constant** at the outer verifier's width (`t(q) → ∞`, `q(N_ν) > ν`). -/
theorem copies_large (s : WS35) (K D : ℕ) :
    ∃ c, ∀ ν, c ≤ 2 ^ ν → K ≤ copies h0 h1 (Outer.width s.mw s.SV (2 ^ ν)) := by
  obtain ⟨Q, hQ⟩ := Filter.tendsto_atTop_atTop.1 (schedule h0 h1 s.k (Outer.apad s.mw s.SV) D).t_tendsto K
  refine ⟨2 ^ Q, fun ν hν => ?_⟩
  have hνQ : Q ≤ ν := (Nat.pow_le_pow_iff_right (by norm_num)).mp hν
  have hw := W3.NearCubicWires.RepairSource.Outer3.nu_lt_width s.mw s.SV ν
  exact hQ _ (by omega)

end

/-- The parameter record of the recovered language: `G` = the amplifier's degree, `d_G = D`, the copy schedule `t(q)+1`, the
selector `a(n) = prefixS … n` the program's scan computes. -/
noncomputable def wq {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (s : WS35) {c d : ℕ} (amp : OrdinaryScheduleAmplifier c d)
    (D : ℕ) : WQ :=
  ⟨d, D, copies h0 h1, 0, fun n => CertPrefix.prefixS s.k (Outer.apad s.mw s.SV) (zu ζ) (zv ζ) D n, c, amp⟩

/-- A nonzero source index satisfies the schedule's length condition `m_a ≤ n/2`. -/
theorem index_fits {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (s : WS35) (D n : ℕ) (h : index s D h0 h1 n ≠ 0) :
    (schedule h0 h1 s.k (Outer.apad s.mw s.SV) D).coreLength (index s D h0 h1 n) ≤ n / 2 := by
  unfold index sched35 LengthSchedule.sourceIdx at *
  exact Nat.findGreatest_of_ne_zero (P := fun a => (schedule h0 h1 s.k (Outer.apad s.mw s.SV) D).coreLength a ≤ n / 2)
    (n := n) rfl h

/-- The live length condition is the schedule's core length (`m_a = t(q) q₀(q)`). -/
theorem coreArity_eq {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (s : WS35) {c d : ℕ} (amp : OrdinaryScheduleAmplifier c d)
    (D : ℕ) (ν : ℕ) :
    (wq h0 h1 s amp D).coreArity s ν =
      (schedule h0 h1 s.k (Outer.apad s.mw s.SV) D).coreLength ν := rfl

/-- **The recovered language is in `E^NP`**, from the Case-2 kit: for every cutoff and every weak machine `M` within
`o(T)`, an onset above the cutoff and an ordinary `E^NP` certificate of `languageCut … M onset`. -/
theorem existsCertificate (s : WS35) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) {c d : ℕ}
    (amp : OrdinaryScheduleAmplifier c d) (D : ℕ)
    {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (hD : 1 ≤ D)
    (ht : After.HTKit s P (wq h0 h1 s amp D)) (cutoff : ℕ)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n ^ (s.k + 2))) :
    ∃ onset, cutoff ≤ onset ∧ Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
      (languageCut s P amp D h0 h1 M onset)) := by
  classical
  let g : WQ := wq h0 h1 s amp D
  let A := Outer.apad s.mw s.SV
  let HR := s.HR
  have hr : AfterReady s g := afterReady_one s g (copies_pos h0 h1)
    (copies_large h0 h1 s amp.arityCoefficient D) hD
  let ar : AfterRun s P g := Classical.choice (After.afterRun_of s P g hr ht)
  obtain ⟨-, n₀, hn₀⟩ := CertPrefix.prefix_index s.k A D h0 h1
  obtain ⟨e1, e2, e3, onset, _, hcut, r, C, E, hpre⟩ :=
    Stage35.Cert.exists_selected_prefix s.k A (zu ζ) (zv ζ) D (max (max cutoff ar.cutoff) (2 ^ (n₀ + 1))) 0 0
      s.clock HR hD (two_u_lt_v h0 h1) M hM
  let p : Params s P g := ⟨zu ζ, zv ζ, e1, e2, e3, onset, 0, 0, r, ar⟩
  have hon0 : 2 ^ (n₀ + 1) ≤ onset := le_trans (le_max_right _ _) hcut
  have hcutA : ar.cutoff ≤ onset := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcut
  refine ⟨onset, le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcut,
    ⟨Closeout.certificate_of_runs _ (program p) (C + ar.C + 8) (E + ar.E) ?_⟩⟩
  intro n point
  -- the index of the language and of the prefix agree on every live length
  have hidx : ∀ m, onset ≤ 2 ^ m → m ≤ n → n₀ ≤ n := by
    intro m hm hmn
    have : 2 ^ (n₀ + 1) ≤ 2 ^ m := hon0.trans hm
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    omega
  have hsl : n₀ ≤ n → CertPrefix.prefixS s.k A (zu ζ) (zv ζ) D n = index s D h0 h1 n := by
    intro hn
    rw [hn₀ n hn, sliceIdx_eq]
  have hidxle : index s D h0 h1 n ≤ n := Nat.findGreatest_le n
  have hb := hpre (List.ofFn point)
  dsimp only at hb
  obtain ⟨cost, hcost, out, hrun, haddr, hflag, _, hword, hlive⟩ := hb
  rw [List.length_ofFn] at hcost hflag hword hlive
  by_cases hon : onset ≤ NearCubicWires.WireExponent3_5.Cert.srcLen s.k A (zu ζ) (zv ζ) D n
  · -- a live source index: the after-prefix program
    have hn : n₀ ≤ n := hidx _ hon (CertPrefix.prefixS_le _ _ _ _ _ n)
    set ν := index s D h0 h1 n with hνdef
    have hS : CertPrefix.prefixS s.k A (zu ζ) (zv ζ) D n = ν := hsl hn
    have hN : NearCubicWires.WireExponent3_5.Cert.srcLen s.k A (zu ζ) (zv ζ) D n = 2 ^ ν := by
      unfold NearCubicWires.WireExponent3_5.Cert.srcLen; rw [hS]
    rw [hN] at hon hword
    have hν1 : 1 ≤ ν := by
      by_contra h0'
      have : ν = 0 := by omega
      rw [this] at hon
      have : 2 ≤ 2 ^ (n₀ + 1) := Nat.le_self_pow (by omega) 2
      omega
    have har : g.coreArity s ν ≤ n / 2 := by
      rw [coreArity_eq h0 h1 s amp D ν, hνdef]
      exact index_fits h0 h1 s D n (by omega)
    rw [if_pos hon] at hword
    obtain ⟨_, qlen, _, hquery⟩ := hlive (by rw [hN]; exact hon)
    have hf : readTapeBit (out (flagP p)) 0 = true := by
      rw [show out (flagP p) = [decide (onset ≤ NearCubicWires.WireExponent3_5.Cert.srcLen s.k A (zu ζ) (zv ζ) D n)] from hflag, hN]
      simp [readTapeBit, hon]
    obtain ⟨acost, hac, outA, hA', houtA⟩ := ar.run n point ν (HR.output M (2 ^ ν))
      (RepairOrdinary.frame (HR.hierarchy.time (List.ofFn (HR.output M (2 ^ ν))).length).bits)
      hν1 (hcutA.trans hon) har hS.symm
    have haddr' : out (addressP p) = RepairOrdinary.frame (List.ofFn point) := by
      have he := NearCubicWires.RepairSource.CloseoutCommonPrefix.first_address (work g) r s.k
      show out (NearCubicWires.RepairSource.CloseoutCommonPrefix.firstSlots (work g) r s.k
        (NearCubicWires.RepairSource.CloseoutCommonPrefix.address (work g) r)) = _
      rw [he]
      exact haddr
    obtain ⟨final, hready, hout⟩ := live_ready p (List.ofFn point) cost out hrun hf _ hword haddr' qlen hquery
      acost outA hA'
    have hval : languageCut s P amp D h0 h1 M onset n point =
        g.gateCore s P g.amp ν (HR.output M (2 ^ ν))
          (clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point := by
      rw [languageCut_live s P amp D h0 h1 M onset n hon]
      rfl
    refine runs_of_ready p (List.ofFn point) _ _ _ final hready ?_ ?_
    · rw [hout, houtA]
      exact congrArg (fun b : Bool => RepairOrdinary.frame b.toNat.bits) hval.symm
    · exact budget_le C E ar.C ar.E n cost acost hcost hac
  · -- below the onset: `false`
    have hf : readTapeBit (out (flagP p)) 0 = false := by
      rw [show out (flagP p) = [decide (onset ≤ NearCubicWires.WireExponent3_5.Cert.srcLen s.k A (zu ζ) (zv ζ) D n)] from hflag]
      simp [readTapeBit, hon]
    obtain ⟨final, hready, hout⟩ := inactive_ready p (List.ofFn point) cost out hrun hf
    have hval : languageCut s P amp D h0 h1 M onset n point = false := by
      have hdead : ¬ onset ≤ 2 ^ index s D h0 h1 n := by
        intro hl
        have hn : n₀ ≤ n := hidx _ hl hidxle
        apply hon
        unfold NearCubicWires.WireExponent3_5.Cert.srcLen
        rw [hsl hn]
        exact hl
      rw [languageCut_dead s P amp D h0 h1 M onset n hdead]
    refine runs_of_ready p (List.ofFn point) _ _ _ final hready ?_ ?_
    · rw [hout, hval]
    · exact small_le C E ar.C ar.E n cost hcost

end NearCubicGates.Close.Recovery3.Common

