import Lean
import Proof.Wire_3_5.Recovery.RecoveryFamily
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Transfer.LiteralSources
import Proof.Wire_3_5.Ledger.LedgerLengths
import Proof.CaseAnalysis.Language
import W3.Proof.Foundations.SourceRegistry
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguageBase


noncomputable section


/-! # The canonical language with the row-B XOR schedule (P3:3699-3756; D1.3)

Realizes the recovered language: "By Lemma tr:soundness this machine is one-sided. Once its clock is `o(T(N))`, the
refuter consequently returns a rejected hierarchy yes-instance at every sufficiently large `N`" (P3:3699-3702), and
"For source lengths `N_a = 2^a`, put `m_a = t(q(N_a))q_0(N_a)`. Choose the largest `a` such that `m_a ≤ n/2`, and extend
the selected core to `n` inputs by ignoring the suffix" (P3:3738-3741), with Case 1 or Case 2's core at the refuter's
rejected yes-instance (P3:3704-3729; base `CloseoutLanguage.core`).

Paper quantities:
* the hierarchy and its refuter: the literals' source bundle (`Literals.eightSources`) at the clock `N^{kclk+2}`
  (`recRefuter`), whose hierarchy language `recL` is in `NTIME(N^{kclk+2})` (`recL_inNTIME`);
* the union setup at that language (`recSetup`: `unionSetupS1` at `recL`), the machine `recMachine U P = U.build P recL`;
* the XOR schedule `t(q) + 1` (`recCopies`; one copy beyond `sched(L(q))`, so the Case-2 advantage is strictly below
  `e_{t(q)}`) on the ledger's width `q(2^a)` (`recSchedule`, the `LengthSchedule` with its length lemmas);
* **`recLanguage`**: at length `n`, the core of the selected source index `a(n)`, of the padded PCP of `recSetup`, at the
  refuter's output for `recMachine` at `2^{a(n)}`;
* **`rejected_yes_eventually`**: past an onset, the refuter's output is a yes-instance the machine rejects
  (the refuter's separation, `U.soundness` and `U.time`'s `o(T)`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)

section Language
variable (l : Literals) (G : Split.Gate)

/-- The hierarchy and its refuter at the clock `N^{kclk+2}` (P3:3633, 3699-3702). -/
noncomputable def recRefuter (kclk : ℕ) : HierarchyRefuterAlgorithm (fun n => n ^ (kclk + 2)) :=
  l.eightSources.hierarchy kclk

/-- The hierarchy language. -/
noncomputable def recL (kclk : ℕ) : Language := fun n x => (recRefuter l kclk).hierarchy.timedView.accepts n x

theorem recL_inNTIME (kclk : ℕ) : InNTIME (fun n => n ^ (kclk + 2)) (recL l kclk) :=
  ⟨(recRefuter l kclk).hierarchy, fun n x => hierarchy_language_exact _ n x⟩

-- The canonical language of the old outer step (`recLanguage`, the core of the hierarchy PCP) is replaced by the
-- three-way core of the recovery (Cases 1a, 1b, 2 at the pair `Γ*`).

end Language

/-! ## The refuter's rejected yes-instances -/

section Refuter

end Refuter

end NearCubicWires.WireExponent3_5.Transfer

end
