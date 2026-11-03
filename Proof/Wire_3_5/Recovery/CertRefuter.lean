import Proof.Wire_3_5.Recovery.CertPrefix
import Proof.CaseAnalysis.ScheduleRefuterPrefixBound
import Proof.Amplification.RecoveryRefuterReplayWhole

/-! # The hybrid program's refuter prefix (P3:3738-3741, 3758-3759; D1.6 B)

Realizes "Run the fixed refuter […] on the source length `N_{a(n)}`" (P3:3758-3759) at the source length the paper's
schedule chooses, "Choose the largest `a` such that `m_a ≤ n/2`" (P3:3738-3740): the scan prefix (M21's
`prefixCold`, index `S = prefixS … n`, `N = 2^S`) under base's onset guard (`CloseoutSchedule.Guarded`), then base's
retained refuter call (`RefuterPrefix.program`, generic in the guarded machine). This restates base's
`RefuterPrefix.selectedProgram`/`exists_selected`, whose guarded machine is v8's fixed-copies `Cold.machine`.

Donors checked: base `RefuterPrefix.program`, `prefix_run`, `budget_bound` (generic, used),
`RecoveryRefuterReplay.polynomial_runs` (used), `prefix_guarded` (used); base `Guarded.exists_guarded`
(v8's width schedule, replaced by M21).

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

end

end NearCubicWires.WireExponent3_5.Cert
