import Lean
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.HybridLedgerOk
import Proof.Wire_3_5.Stage35.Lang
import W3.Proof.CaseAnalysis.Language


/-!
# The recovered language of row B (the three-way hard core at the row-B schedule)

Paper v2, §H.5 "The common hard core" (Cases 1a Hard word, 1b Hard oracle, 2 Hard proof table, with the first accepted
oracle `O*` chosen before the proof circuit) and §H.6 "Exact lengths and canonical recovery" ("For source lengths
`N_a = 2^a`, put `m_a = t(q(N_a)) q_0(N_a)`. Choose the largest `a` such that `m_a ≤ n/2`, and extend the selected
core to `n` inputs by ignoring the suffix").

At the literals `l`:
* `ws l`: the clock exponent `kclk`, the refuter of the source bundle at the clock `N^{kclk+2}`
  (`l.eightSources.hierarchy kclk`), the short-PCP source `gateMW l` and the succinct verifier `gateSV l` of the
  refuter's hierarchy `gateH l` (Lemma H.6);
* `recSched l`: the row-B length schedule at the padded width `q(N) = gateWidth l N`, the XOR schedule `t(q) + 1` and
  the clause degree `d_G = recDG l`; `sliceWidth l n = q(2^{a(n)})`;
* **`recLanguage2 l M`**: at length `n`, the slice `F_n` — the three-way core `coreC` at the refuter's word for `M` at
  `2^{a(n)}` with `t(q)+1` copies and clause width `⌈d_G log₂(q+2)⌉`, Case 1 through the source bundle's amplifier at
  the oracle degree `17·c_STV` (`l.eightSources.amplification.schedule`; `Stage35.slice`);
* **`recLanguageCut2 l M cutoff`** (`false` while `2^{a(n)}` is below the cutoff);
* **`Split.CertGen l`**: the recovered language is in `E^NP` for every weak machine within `o(T)`.
-/

set_option autoImplicit false


namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Ledger
open _root_.NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)

variable (l : Literals)

/-- The fixed objects the case split and the recovery read, at the literals `l`. -/
noncomputable def ws : Stage35.WS35 :=
  ⟨kclk, PolynomialClock.ordinaryClock kclk, l.eightSources.hierarchy kclk, gateMW l, lenG l, gateSV l⟩

/-- The row-B length schedule at the padded width `q(2^a)`, with `t(q)+1` copies and the clause degree `d_G`. -/
noncomputable def recSched : LengthSchedule := Stage35.sched35 (ws l) (recDG l) (gateZeta_pos l) (gateZeta_lt l)

/-- The width `q(2^{a(n)})` of the slice `n`. -/
noncomputable def sliceWidth (n : ℕ) : ℕ := nativeWidth kclk (gateApad l) (2 ^ (recSched l).sourceIdx n)

/-- **The recovered language** at the weak machine `M`: the slice `F_n` of the three-way core. -/
noncomputable def recLanguage2 (M : OrdinaryWeakMachine) : Language :=
  Stage35.language (ws l) (gatePCPP l) l.eightSources.amplification.schedule (recDG l) (gateZeta_pos l) (gateZeta_lt l) M

/-- **The recovered language with a cutoff**: `false` while `2^{a(n)}` is below the cutoff. -/
noncomputable def recLanguageCut2 (M : OrdinaryWeakMachine) (cutoff : ℕ) : Language :=
  Stage35.languageCut (ws l) (gatePCPP l) l.eightSources.amplification.schedule (recDG l) (gateZeta_pos l) (gateZeta_lt l) M cutoff

/-- The slice in closed form: the three-way core at `a = a(n)`, `z` the refuter's word for `M` at `2^a`, `t(q)+1`
copies and clause width `⌈d_G log₂(q+2)⌉` at `q = sliceWidth l n`. -/
theorem recLanguage2_eq (M : OrdinaryWeakMachine) (n : ℕ) :
    recLanguage2 l M n =
      W3.NearCubicWires.RepairSource.Outer3.coreC (gateMW l) (gateSV l) (gatePCPP l)
        l.eightSources.amplification.schedule ((recSched l).sourceIdx n)
        ((recRefuter l kclk).output M (2 ^ (recSched l).sourceIdx n))
        (recCopies (gateZeta_pos l) (gateZeta_lt l) (sliceWidth l n)) (clauseWidth (recDG l) (sliceWidth l n)) n :=
  rfl

theorem recLanguageCut2_eq (M : OrdinaryWeakMachine) (cutoff n : ℕ) :
    recLanguageCut2 l M cutoff n =
      if cutoff ≤ 2 ^ (recSched l).sourceIdx n then recLanguage2 l M n else fun _ => false := rfl

end NearCubicWires.WireExponent3_5.Transfer

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary

/-- **D1.6 (the recovered language is in `E^NP`)**: for every weak machine within `o(N^{kclk+2})`, a cutoff and an
ordinary `E^NP` certificate of the recovered language at that machine. -/
def CertGen (l : Literals) : Prop :=
  ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M (fun n => n ^ (Transfer.kclk + 2)) →
    ∃ cutoff : ℕ, Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat (Transfer.recLanguageCut2 l M cutoff))

end NearCubicWires.WireExponent3_5.Split

