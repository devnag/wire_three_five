import Proof.CaseAnalysis.CommonPrefixFields
import Proof.CaseAnalysis.CommonPrefixProgram
import Proof.CaseAnalysis.CommonPrepareBudget
import Proof.Wire_3_5.Recovery.CertRefuter

/-!
# The recovery program's prefix at a given hierarchy refuter

Paper v2, §H.6: "For source lengths `N_a = 2^a`, put `m_a = t(q(N_a)) q_0(N_a)`. Choose the largest `a` such that
`m_a ≤ n/2` […] Run the fixed refuter to obtain `z`". The scan prefix (`Cert.selectedProgram`: the index
`S = prefixS … n` by the upward scan with the row-B XOR schedule, under the onset guard, then the retained refuter
call) and the paid preparation of the hierarchy word `frame z ++ frame (H.time |z|).bits`, restated with the refuter
`HR` as a parameter (the earlier form read it from a source bundle; nothing else of the bundle is used).

Paper quantity of the main type (`exists_selected_prefix`): the prefix's outputs at `N = 2^{a(n)}` — the onset flag,
the refuter's word `z` with the hierarchy's time bits, and the conflict `M` rejects `z` iff the hierarchy accepts it —
within a polynomial clock.
-/

set_option autoImplicit false

namespace Stage35.Cert
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutSchedule NearCubicWires.RepairSource.CloseoutRetainedRefuter
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairSource.CloseoutCommonPrefix
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cert (selectedProgram srcLen srcLen_le)

noncomputable section

/-- **The refuter prefix**: one onset and refuter for all input lengths; on every input it keeps the address, writes
the flag `[onset ≤ N]` and the refuter's answer at `N` when live, within a polynomial clock. -/
theorem exists_selected (k A u v D cutoff : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2)))
    (hD : 1 ≤ D) (huv : 2 * u < v) (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n ^ (k + 2))) :
    ∃ e1 e2 e3 : ℕ, ∃ onset : ℕ, 1 ≤ onset ∧ cutoff ≤ onset ∧ ∃ (r : OrdinaryOracleProgram) (C E : ℕ),
      ∀ bits : List Bool,
        let w := CertPrefixPrep.prefixTapes D
        let N := srcLen k A u v D bits.length
        let answer := List.ofFn (HR.output M N)
        ∃ cost ≤ C * (2 ^ bits.length + 1) ^ E, ∃ out,
          Ready RecoveryOracle.correctedSat (selectedProgram k A u v D e1 e2 e3 onset r)
            cost (input r (Guarded.input w bits)) out ∧
          out (old r (RefuterPrefix.addressPort w)) = RepairOrdinary.frame bits ∧
          out (old r (RefuterPrefix.flagPort w)) = [decide (onset ≤ N)] ∧
          out (fresh (Guarded.tapes w) r 0) = RepairOrdinary.frame (if onset ≤ N then answer else []) ∧
          (onset ≤ N →
            (M.accepts N (HR.output M N) ↔
              HR.hierarchy.timedView.accepts N
                (HR.output M N) = false) ∧
            ∃ qlen ≤ C * (2 ^ bits.length + 1) ^ E,
              out (bank r (RefuterPrefix.sourcePort w) (clocked r).queryTape) = List.replicate qlen false) := by
  obtain ⟨b, e, start, r, _hb, _he, hrefuter⟩ := RecoveryRefuterReplay.polynomial_runs
    HR clock M hM
  obtain ⟨e1, e2, e3, coef, E0, hg⟩ := CertPrefix.prefix_guarded k A u v D hD huv
  let onset := max (max 1 cutoff) start
  have ho : 1 ≤ onset := (Nat.le_max_left 1 cutoff).trans (Nat.le_max_left _ _)
  have hcut : cutoff ≤ onset := (Nat.le_max_right 1 cutoff).trans (Nat.le_max_left _ _)
  let a := coef + 6 * onset + 41
  refine ⟨e1, e2, e3, onset, ho, hcut, r, 32 * (a + b * 2 ^ e + 1), (E0 + 1) + e + 1, ?_⟩
  intro bits
  let w := CertPrefixPrep.prefixTapes D
  let N := srcLen k A u v D bits.length
  let answer := List.ofFn (HR.output M N)
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


/-- The two pieces: the refuter prefix, then the paid preparation. -/
def prefixPieces (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram)
    (j : Fin 2) : Piece (CloseoutCommonPrefix.tapes (CertPrefixPrep.prefixTapes D) r k) :=
  if j.val = 0 then
    focused (selectedProgram k A u v D e1 e2 e3 onset r) (firstSlots (CertPrefixPrep.prefixTapes D) r k)
  else ordinary (RecoveryFocus.machine (prepareSlots (CertPrefixPrep.prefixTapes D) r k)
    (CloseoutCommonPrepare.machine k HR.hierarchy.coefficient Aw Bw))

def prefixNext (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram)
    (j : Fin 2) (_ : Fin (prefixPieces k A u v D e1 e2 e3 onset Aw Bw HR r j).states)
    (_ : Fin (CloseoutCommonPrefix.tapes (CertPrefixPrep.prefixTapes D) r k) → Bool) : Option (Fin 2) :=
  if j.val = 0 then some 1 else none

/-- **The hybrid program's common prefix.** -/
def prefixProgram (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram) :=
  (CloseoutCommonPrefix.ports (CertPrefixPrep.prefixTapes D) r k).program
    (graph (prefixPieces k A u v D e1 e2 e3 onset Aw Bw HR r) 0
      (prefixNext k A u v D e1 e2 e3 onset Aw Bw HR r))

theorem prefix_run (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram)
    (bits result : List Bool) (fuel : ℕ)
    (a : Fin (CloseoutCommonPrefix.base (CertPrefixPrep.prefixTapes D) r) → List Bool)
    (hpre : Ready RecoveryOracle.correctedSat (selectedProgram k A u v D e1 e2 e3 onset r) fuel
      (CloseoutRetainedRefuter.input r (Guarded.input (CertPrefixPrep.prefixTapes D) bits)) a)
    (ha : a (address (CertPrefixPrep.prefixTapes D) r) = RepairOrdinary.frame bits)
    (hb : a (answer (CertPrefixPrep.prefixTapes D) r) = RepairOrdinary.frame result) :
    let w := CertPrefixPrep.prefixTapes D
    let H := HR.hierarchy
    ∃ cost ≤ fuel + CloseoutCommonPrepare.budget k H.coefficient Aw Bw bits result + 2, ∃ out,
      Ready RecoveryOracle.correctedSat (prefixProgram k A u v D e1 e2 e3 onset Aw Bw HR r)
        cost (CloseoutCommonPrefix.input w r k bits) out ∧
      out (firstSlots w r k (address w r)) = RepairOrdinary.frame bits ∧
      out (prepareSlots w r k (CloseoutCommonPrepare.capacitySlot k)) =
        List.replicate (CloseoutCapacity.capacity Aw Bw bits.length) true ∧
      out (prepareSlots w r k (CloseoutCommonPrepare.hierarchySlot k)) =
        RepairOrdinary.frame result ++ RepairOrdinary.frame (H.time result.length).bits ∧
      ∀ i : Fin (CloseoutCommonPrefix.base w r), i ≠ address w r → i ≠ answer w r →
        out (firstSlots w r k i) = a i := by
  let w := CertPrefixPrep.prefixTapes D
  let H := HR.hierarchy
  let ps := CloseoutCommonPrefix.ports w r k
  let parts := prefixPieces k A u v D e1 e2 e3 onset Aw Bw HR r
  let follow := prefixNext k A u v D e1 e2 e3 onset Aw Bw HR r
  let middle := install (firstSlots w r k) (CloseoutCommonPrefix.input w r k bits) a
  have hfirst := hpre.focus ps (firstSlots w r k) (first_injective w r k) rfl
    (CloseoutCommonPrefix.input w r k bits) (initial_first w r k bits)
  obtain ⟨prepared, hp, haddress, hW, hword⟩ := CloseoutCommonPrepare.run H Aw Bw bits result
  have hfocus := hp.focus (prepareSlots w r k) (prepare_injective w r k) middle
    (middle_input w r k bits result a ha hb)
  obtain ⟨c, hc, hlast⟩ := RecoveryPrefixCold.ordinary_ready (o := RecoveryOracle.correctedSat)
    ps _ _ _ hfocus
  have ta := hfirst.call ps parts 0 follow 0 1 (by intro q; rfl)
  have tb := hlast.stop ps parts 0 follow 1 (by intro q; rfl)
  have ht := trans ta tb
  have hi : controlConfig (RecoveryCalls.code (fun j => (parts j).states) 0)
      (initialConfiguration (parts 0).machine (CloseoutCommonPrefix.input w r k bits)) =
      initialConfiguration (prefixProgram k A u v D e1 e2 e3 onset Aw Bw HR r).base.machine
        (CloseoutCommonPrefix.input w r k bits) := rfl
  rw [hi] at ht
  refine ⟨(fuel + 1) + (c + 1), by dsimp only [H] at hc; omega, _, ⟨_, ht, ?_, fun _ => rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp [prefixProgram, Ports.program, graph, RecoveryCalls.machine, RecoveryCalls.stopped, parts]
  · rw [← prepare_address]
    exact (install_slot _ (prepare_injective w r k) _ _ _).trans haddress
  · exact (install_slot _ (prepare_injective w r k) _ _ _).trans hW
  · exact (install_slot _ (prepare_injective w r k) _ _ _).trans hword
  · intro i hai hbi
    exact (install_other _ _ _ _ (prepare_ne_old w r k i hai hbi)).trans
      (install_slot _ (first_injective w r k) _ _ i)

/-- **The hybrid program's prefix on every input**: one onset, refuter and preparation constants for all lengths. -/
theorem exists_selected_prefix (k A u v D cutoff Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2))) (hD : 1 ≤ D) (huv : 2 * u < v)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n ^ (k + 2))) :
    ∃ e1 e2 e3 : ℕ, ∃ onset : ℕ, 1 ≤ onset ∧ cutoff ≤ onset ∧ ∃ (r : OrdinaryOracleProgram) (C E : ℕ),
      ∀ bits : List Bool,
        let w := CertPrefixPrep.prefixTapes D
        let H := HR
        let N := srcLen k A u v D bits.length
        let result := if onset ≤ N then List.ofFn (H.output M N) else []
        ∃ cost ≤ C * (2 ^ bits.length + 1) ^ E, ∃ out,
          Ready RecoveryOracle.correctedSat (prefixProgram k A u v D e1 e2 e3 onset Aw Bw HR r)
            cost (CloseoutCommonPrefix.input w r k bits) out ∧
          out (0 : Fin (CloseoutCommonPrefix.tapes w r k)) = RepairOrdinary.frame bits ∧
          out (firstSlots w r k (old r (RefuterPrefix.flagPort w))) = [decide (onset ≤ N)] ∧
          out (prepareSlots w r k (CloseoutCommonPrepare.capacitySlot k)) =
            List.replicate (CloseoutCapacity.capacity Aw Bw bits.length) true ∧
          out (prepareSlots w r k (CloseoutCommonPrepare.hierarchySlot k)) =
            RepairOrdinary.frame result ++ RepairOrdinary.frame (H.hierarchy.time result.length).bits ∧
          (onset ≤ N →
            (M.accepts N (H.output M N) ↔ H.hierarchy.timedView.accepts N (H.output M N) = false) ∧
            ∃ qlen ≤ C * (2 ^ bits.length + 1) ^ E,
              out (firstSlots w r k (query w r)) = List.replicate qlen false) := by
  obtain ⟨e1, e2, e3, onset, honset, hcut, r, C, E, hprefix⟩ :=
    exists_selected k A u v D cutoff clock HR hD huv M hM
  let H := HR
  let cp := CloseoutCommonPrepare.coefficient k H.hierarchy.coefficient Aw Bw
  let ep := CloseoutCommonPrepare.degree Aw
  refine ⟨e1, e2, e3, onset, honset, hcut, r, 32 * (C + cp * 2 ^ ep + 1), E + ep + 1, ?_⟩
  intro bits
  let w := CertPrefixPrep.prefixTapes D
  let N := srcLen k A u v D bits.length
  let result := if onset ≤ N then List.ofFn (H.output M N) else []
  have hN : N ≤ 2 ^ bits.length := srcLen_le k A u v D bits.length
  have hlength : result.length ≤ 2 ^ bits.length := by
    dsimp only [result]
    split_ifs
    · simpa only [List.length_ofFn] using hN
    · simp
  obtain ⟨fuel, hfuel, a, hpre, ha, hflag, hanswer, hquery⟩ := hprefix bits
  obtain ⟨cost, hcost, out, hr, haddress, hW, hword, hkeep⟩ :=
    prefix_run k A u v D e1 e2 e3 onset Aw Bw HR r bits result fuel a hpre ha hanswer
  have hprep := CloseoutCommonPrepare.budget_bound k H.hierarchy.coefficient Aw Bw bits result hlength
  have hpower : cp * (2 ^ bits.length + 1) ^ ep ≤ cp * (2 ^ bits.length + 2) ^ ep :=
    Nat.mul_le_mul_left cp (Nat.pow_le_pow_left (by omega) ep)
  have hbound := RefuterPrefix.budget_bound C E cp ep bits.length (2 ^ bits.length) (Nat.le_refl _)
  have hsmall : C * (2 ^ bits.length + 1) ^ E ≤ 32 * (C + cp * 2 ^ ep + 1) * (2 ^ bits.length + 1) ^ (E + ep + 1) := by
    have hnonneg : 0 ≤ 16 * (cp * (2 ^ bits.length + 2) ^ ep + 1) + 4 := Nat.zero_le _
    omega
  have htotal : cost ≤ 32 * (C + cp * 2 ^ ep + 1) * (2 ^ bits.length + 1) ^ (E + ep + 1) := by
    change CloseoutCommonPrepare.budget k H.hierarchy.coefficient Aw Bw bits result ≤
      cp * (2 ^ bits.length + 1) ^ ep at hprep
    change cost ≤ fuel + CloseoutCommonPrepare.budget k H.hierarchy.coefficient Aw Bw bits result + 2 at hcost
    omega
  have hfaddr : old r (RefuterPrefix.flagPort w) ≠ address w r := by
    intro he
    exact (Guarded.old_fresh w (Cold.extra w 0) 4) ((old_injective r he).symm)
  have hfanswer := old_fresh r (RefuterPrefix.flagPort w) 0
  refine ⟨cost, htotal, out, hr, ?_, (hkeep _ hfaddr hfanswer).trans hflag, hW, hword, ?_⟩
  · simpa only [first_address] using haddress
  · intro hn
    obtain ⟨hconflict, qlen, hqlen, hqt⟩ := hquery hn
    refine ⟨hconflict, qlen, hqlen.trans hsmall, ?_⟩
    exact (hkeep (query w r) (query_ne_address w r)
      (bank_fresh r (RefuterPrefix.sourcePort w) (clocked r).queryTape 0)).trans hqt

end

end Stage35.Cert
