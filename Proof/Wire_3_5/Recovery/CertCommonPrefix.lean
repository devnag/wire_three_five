import Proof.Wire_3_5.Recovery.CertRefuter

/-! # The hybrid program's common prefix (P3:3738-3741, 3758-3759; D1.6 B)

Realizes, for the hybrid slice, the prefix of "The resulting slice is computable in `E^NP`. Run the fixed refuter
[…] on the source length `N_{a(n)}`" (P3:3758-3759): the refuter prefix (`Cert.selectedProgram`, at
`N = 2^{a(n)}`), then base's paid preparation of the recovery's shared words (`CloseoutCommonPrepare.machine`: the
capacity `1^W` and the hierarchy request word `frame answer ++ frame (H.time |answer|).bits`). Base's
`CloseoutCommonPrefix` layout, ports and field lemmas are generic in the guarded workspace `w` and are used unchanged
at `w = prefixTapes D`; this module restates `pieces`/`program`, `prefix_run` and `exists_selected`, which name the Theorem 2.5 repository's
`RefuterPrefix.selectedProgram` and `Step.workTapes`.

Donors checked: base `CloseoutCommonPrefix.{firstSlots, prepareSlots, input, ports, query,
initial_first, middle_input, prepare_address, …}` (generic, used), `CloseoutCommonPrepare.run`/`budget_bound` (used),
`RecoveryPrefixCold.ordinary_ready` (used).

Paper quantity of the main type (`exists_selected`): the prefix's outputs, the onset flag, the recovery's shared
capacity and hierarchy word at `N = 2^{a(n)}`, within a polynomial clock. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Cert
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutSchedule NearCubicWires.RepairSource.CloseoutRetainedRefuter
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairSource.CloseoutCommonPrefix
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.Transfer

noncomputable section

/-- The two pieces: the refuter prefix, then the paid preparation. -/
def prefixPieces (sources : EightSources) (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram)
    (j : Fin 2) : Piece (CloseoutCommonPrefix.tapes (CertPrefixPrep.prefixTapes D) r k) :=
  if j.val = 0 then
    focused (selectedProgram k A u v D e1 e2 e3 onset r) (firstSlots (CertPrefixPrep.prefixTapes D) r k)
  else ordinary (RecoveryFocus.machine (prepareSlots (CertPrefixPrep.prefixTapes D) r k)
    (CloseoutCommonPrepare.machine k (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy.coefficient Aw Bw))

def prefixNext (sources : EightSources) (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram)
    (j : Fin 2) (_ : Fin (prefixPieces sources k A u v D e1 e2 e3 onset Aw Bw clock r j).states)
    (_ : Fin (CloseoutCommonPrefix.tapes (CertPrefixPrep.prefixTapes D) r k) → Bool) : Option (Fin 2) :=
  if j.val = 0 then some 1 else none

/-- **The hybrid program's common prefix.** -/
def prefixProgram (sources : EightSources) (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram) :=
  (CloseoutCommonPrefix.ports (CertPrefixPrep.prefixTapes D) r k).program
    (graph (prefixPieces sources k A u v D e1 e2 e3 onset Aw Bw clock r) 0
      (prefixNext sources k A u v D e1 e2 e3 onset Aw Bw clock r))

theorem prefix_run (sources : EightSources) (k A u v D e1 e2 e3 onset Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (r : OrdinaryOracleProgram)
    (bits result : List Bool) (fuel : ℕ)
    (a : Fin (CloseoutCommonPrefix.base (CertPrefixPrep.prefixTapes D) r) → List Bool)
    (hpre : Ready RecoveryOracle.correctedSat (selectedProgram k A u v D e1 e2 e3 onset r) fuel
      (CloseoutRetainedRefuter.input r (Guarded.input (CertPrefixPrep.prefixTapes D) bits)) a)
    (ha : a (address (CertPrefixPrep.prefixTapes D) r) = RepairOrdinary.frame bits)
    (hb : a (answer (CertPrefixPrep.prefixTapes D) r) = RepairOrdinary.frame result) :
    let w := CertPrefixPrep.prefixTapes D
    let H := (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
    ∃ cost ≤ fuel + CloseoutCommonPrepare.budget k H.coefficient Aw Bw bits result + 2, ∃ out,
      Ready RecoveryOracle.correctedSat (prefixProgram sources k A u v D e1 e2 e3 onset Aw Bw clock r)
        cost (CloseoutCommonPrefix.input w r k bits) out ∧
      out (firstSlots w r k (address w r)) = RepairOrdinary.frame bits ∧
      out (prepareSlots w r k (CloseoutCommonPrepare.capacitySlot k)) =
        List.replicate (CloseoutCapacity.capacity Aw Bw bits.length) true ∧
      out (prepareSlots w r k (CloseoutCommonPrepare.hierarchySlot k)) =
        RepairOrdinary.frame result ++ RepairOrdinary.frame (H.time result.length).bits ∧
      ∀ i : Fin (CloseoutCommonPrefix.base w r), i ≠ address w r → i ≠ answer w r →
        out (firstSlots w r k i) = a i := by
  let w := CertPrefixPrep.prefixTapes D
  let H := (sources.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy
  let ps := CloseoutCommonPrefix.ports w r k
  let parts := prefixPieces sources k A u v D e1 e2 e3 onset Aw Bw clock r
  let follow := prefixNext sources k A u v D e1 e2 e3 onset Aw Bw clock r
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
      initialConfiguration (prefixProgram sources k A u v D e1 e2 e3 onset Aw Bw clock r).base.machine
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
theorem exists_selected_prefix (sources : EightSources) (k A u v D cutoff Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (hD : 1 ≤ D) (huv : 2 * u < v)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n ^ (k + 2))) :
    ∃ e1 e2 e3 : ℕ, ∃ onset : ℕ, 1 ≤ onset ∧ cutoff ≤ onset ∧ ∃ (r : OrdinaryOracleProgram) (C E : ℕ),
      ∀ bits : List Bool,
        let w := CertPrefixPrep.prefixTapes D
        let H := sources.hierarchy (fun n => n ^ (k + 2)) clock
        let N := srcLen k A u v D bits.length
        let result := if onset ≤ N then List.ofFn (H.output M N) else []
        ∃ cost ≤ C * (2 ^ bits.length + 1) ^ E, ∃ out,
          Ready RecoveryOracle.correctedSat (prefixProgram sources k A u v D e1 e2 e3 onset Aw Bw clock r)
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
    exists_selected sources k A u v D cutoff clock hD huv M hM
  let H := sources.hierarchy (fun n => n ^ (k + 2)) clock
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
    prefix_run sources k A u v D e1 e2 e3 onset Aw Bw clock r bits result fuel a hpre ha hanswer
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

end NearCubicWires.WireExponent3_5.Cert
