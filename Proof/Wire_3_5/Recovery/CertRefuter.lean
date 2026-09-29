import Proof.Wire_3_5.Recovery.CertPrefix

/-! # The hybrid program's refuter prefix (P3:3738-3741, 3758-3759; D1.6 B)

Realizes "Run the fixed refuter […] on the source length `N_{a(n)}`" (P3:3758-3759) at the source length the paper's
schedule chooses, "Choose the largest `a` such that `m_a ≤ n/2`" (P3:3738-3740): the scan prefix (`prefixCold`, index `S = prefixS … n`, `N = 2^S`) under base's onset guard (`CloseoutSchedule.Guarded`), then base's
retained refuter call (`RefuterPrefix.program`, generic in the guarded machine). This restates base's
`RefuterPrefix.selectedProgram`/`exists_selected`, whose guarded machine is the Theorem 2.5 repository's fixed-copies `Cold.machine`.

Donors checked: base `RefuterPrefix.program`, `prefix_run`, `budget_bound` (generic, used),
`RecoveryRefuterReplay.polynomial_runs` (used), `prefix_guarded` (used); base `Guarded.exists_guarded`
(the Theorem 2.5 repository's width schedule, replaced by M21).

Paper quantity of the main type (`exists_selected`): the refuter's answer at `N = 2^{a(n)}` and the onset flag. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Cert
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutSchedule NearCubicWires.RepairSource.CloseoutRetainedRefuter
open NearCubicWires.RepairSource.OrdinaryOracleCompose
open NearCubicWires.WireExponent3_5.Transfer

noncomputable section

/-- The guarded prefix followed by the retained refuter call. -/
def selectedProgram (k A u v D e1 e2 e3 onset : ℕ) (r : OrdinaryOracleProgram) :=
  RefuterPrefix.program (Guarded.machine (CertPrefix.prefixCold k A u v D e1 e2 e3) onset) r
    (RefuterPrefix.sourcePort (CertPrefixPrep.prefixTapes D)) (RefuterPrefix.flagPort (CertPrefixPrep.prefixTapes D))

/-- The source length of the hybrid slice at input length `n`: `N = 2^{S}`, `S = prefixS … n`. -/
def srcLen (k A u v D n : ℕ) : ℕ := 2 ^ CertPrefix.prefixS k A u v D n

theorem srcLen_le (k A u v D n : ℕ) : srcLen k A u v D n ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by norm_num) (CertPrefix.prefixS_le k A u v D n)

/-- **The refuter prefix**: one onset and refuter for all input lengths; on every input it keeps the address, writes
the flag `[onset ≤ N]` and the refuter's answer at `N` when live, within a polynomial clock. -/
theorem exists_selected (sources : EightSources) (k A u v D cutoff : ℕ) (clock : OrdinaryClock (fun n => n ^ (k + 2)))
    (hD : 1 ≤ D) (huv : 2 * u < v) (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n ^ (k + 2))) :
    ∃ e1 e2 e3 : ℕ, ∃ onset : ℕ, 1 ≤ onset ∧ cutoff ≤ onset ∧ ∃ (r : OrdinaryOracleProgram) (C E : ℕ),
      ∀ bits : List Bool,
        let w := CertPrefixPrep.prefixTapes D
        let N := srcLen k A u v D bits.length
        let answer := List.ofFn ((sources.hierarchy (fun n => n ^ (k + 2)) clock).output M N)
        ∃ cost ≤ C * (2 ^ bits.length + 1) ^ E, ∃ out,
          Ready RecoveryOracle.correctedSat (selectedProgram k A u v D e1 e2 e3 onset r)
            cost (input r (Guarded.input w bits)) out ∧
          out (old r (RefuterPrefix.addressPort w)) = RepairOrdinary.frame bits ∧
          out (old r (RefuterPrefix.flagPort w)) = [decide (onset ≤ N)] ∧
          out (fresh (Guarded.tapes w) r 0) = RepairOrdinary.frame (if onset ≤ N then answer else []) ∧
          (onset ≤ N →
            (M.accepts N ((sources.hierarchy (fun n => n ^ (k + 2)) clock).output M N) ↔
              (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.timedView.accepts N
                ((sources.hierarchy (fun n => n ^ (k + 2)) clock).output M N) = false) ∧
            ∃ qlen ≤ C * (2 ^ bits.length + 1) ^ E,
              out (bank r (RefuterPrefix.sourcePort w) (clocked r).queryTape) = List.replicate qlen false) := by
  obtain ⟨b, e, start, r, _hb, _he, hrefuter⟩ := RecoveryRefuterReplay.polynomial_runs
    (sources.hierarchy (fun n => n ^ (k + 2)) clock) clock M hM
  obtain ⟨e1, e2, e3, coef, E0, hg⟩ := CertPrefix.prefix_guarded k A u v D hD huv
  let onset := max (max 1 cutoff) start
  have ho : 1 ≤ onset := (Nat.le_max_left 1 cutoff).trans (Nat.le_max_left _ _)
  have hcut : cutoff ≤ onset := (Nat.le_max_right 1 cutoff).trans (Nat.le_max_left _ _)
  let a := coef + 6 * onset + 41
  refine ⟨e1, e2, e3, onset, ho, hcut, r, 32 * (a + b * 2 ^ e + 1), (E0 + 1) + e + 1, ?_⟩
  intro bits
  let w := CertPrefixPrep.prefixTapes D
  let N := srcLen k A u v D bits.length
  let answer := List.ofFn ((sources.hierarchy (fun n => n ^ (k + 2)) clock).output M N)
  obtain ⟨mid, hm, haddress, hflag, hword⟩ := hg bits onset
  have hN : N ≤ 2 ^ bits.length := srcLen_le k A u v D bits.length
  have hrun : decide (onset ≤ N) = true →
      OrdinaryOracleRuns RecoveryOracle.correctedSat r (List.replicate N true) answer (b * (N + 2) ^ e) := by
    intro h
    exact (hrefuter N ((Nat.le_max_right (max 1 cutoff) start).trans (of_decide_eq_true h))).1
  obtain ⟨cost, hcost, out, hr, hret, hout, hquery⟩ := RefuterPrefix.prefix_run
    (Guarded.machine (CertPrefix.prefixCold k A u v D e1 e2 e3) onset) r
    (RefuterPrefix.sourcePort w) (RefuterPrefix.flagPort w) (Guarded.input w bits) mid (List.replicate N true) answer
    (decide (onset ≤ N)) hm hflag hword hrun
  have hX : 1 ≤ 2 ^ bits.length + 1 := by omega
  have hpow : (2 ^ bits.length + 1) ^ E0 ≤ (2 ^ bits.length + 1) ^ (E0 + 1) := Nat.pow_le_pow_right hX (by omega)
  have hone : 2 ^ bits.length + 1 ≤ (2 ^ bits.length + 1) ^ (E0 + 1) := by
    calc 2 ^ bits.length + 1 = (2 ^ bits.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ bits.length + 1) ^ (E0 + 1) := Nat.pow_le_pow_right hX (by omega)
  have hfuel : coef * (2 ^ bits.length + 1) ^ E0 + 1 + (6 * onset + 18) + 1 + (6 * N + 15) ≤
      a * (2 ^ bits.length + 1) ^ (E0 + 1) := by
    have h1 := Nat.mul_le_mul_left coef hpow
    have h2 : 1 ≤ (2 ^ bits.length + 1) ^ (E0 + 1) := Nat.one_le_pow _ _ (by omega)
    have h3 := Nat.mul_le_mul_left (6 * onset + 35) h2
    have e3' : a * (2 ^ bits.length + 1) ^ (E0 + 1) = coef * (2 ^ bits.length + 1) ^ (E0 + 1) +
        (6 * onset + 35) * (2 ^ bits.length + 1) ^ (E0 + 1) + 6 * (2 ^ bits.length + 1) ^ (E0 + 1) := by
      simp only [a]; ring
    omega
  have hbnd := RefuterPrefix.budget_bound a (E0 + 1) b e bits.length N hN
  have hNeq : srcLen k A u v D bits.length = 2 ^ CertPrefix.prefixS k A u v D bits.length := rfl
  have ha : RefuterPrefix.addressPort w ≠ RefuterPrefix.sourcePort w := Guarded.old_fresh w (Cold.extra w 0) 8
  have hfl : RefuterPrefix.flagPort w ≠ RefuterPrefix.sourcePort w := by
    intro h
    have hv := congrArg Fin.val h
    change Cold.tapes w + 4 = Cold.tapes w + 8 at hv
    omega
  refine ⟨cost, by omega, out, hr, (hret _ ha).trans haddress, (hret _ hfl).trans hflag, ?_, ?_⟩
  · simpa using hout
  · intro hn
    have hs : start ≤ N := (Nat.le_max_right (max 1 cutoff) start).trans hn
    obtain ⟨qlen, hqlen, hqt⟩ := hquery (decide_eq_true hn)
    refine ⟨(hrefuter N hs).2, qlen, ?_, hqt⟩
    have : b * (N + 2) ^ e ≤ a * (2 ^ bits.length + 1) ^ (E0 + 1) + 16 * (b * (N + 2) ^ e + 1) + 4 := by omega
    exact (hqlen.trans this).trans hbnd

end

end NearCubicWires.WireExponent3_5.Cert
