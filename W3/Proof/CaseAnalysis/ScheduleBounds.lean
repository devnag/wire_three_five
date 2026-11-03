import W3.Aliases
import W3.Proof.CaseAnalysis.Language
import W3.Proof.Assembly.SelectedRecoveryIntegration
import W3.Proof.Foundations.SourceRegistry

w3_alias_base

namespace W3

/-! The schedule at the anchor's `widthAt` (on `width sources k clock`, q(N) of Lemma C.5), C.12
"The native widths q(N_ν) have bounded additive jumps": the jump is `(k+2)(A_pad+1)` (gates
`Outer.widthOf_step`), the lower bound `ν < q(N_ν)` (gates `Outer.succ_le_widthOf`, `nu_lt_width`). The generic
lemmas are unchanged. -/


/-! Actual fixed-copy core widths and the finite largest-index schedule.
All constants are fixed before the final language input length. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem clause_linear (degree q : Nat) : clauseWidth degree q ≤ degree*(q+1) := by
  have h : q+2 ≤ 2^(q+1) := Nat.succ_le_of_lt (Nat.lt_two_pow_self : q+1 < 2^(q+1))
  apply Nat.clog_le_of_le_pow
  have hp:=Nat.pow_le_pow_left h degree
  simpa only [←pow_mul,Nat.mul_comm] using hp

end
end NearCubicWires.RepairSource.CloseoutLanguage

end W3
