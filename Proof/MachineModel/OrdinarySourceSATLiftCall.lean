import Proof.MachineModel.OrdinarySourceSATLiftParse

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem quiet_trace {o : ℕ → Bool} {t : ℕ} (ports : Ports t) (piece : Piece t)
    (hq : ∀ q,piece.query q=none) (fuel : ℕ) (c : Configuration t piece.states)
    (r : ExecutionReceipt t piece.states) (hr : runFrom piece.machine fuel c=some r) :
    OrdinaryOracleTrace o (ports.program piece) r.steps c r.final := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact .refl _
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; exact .refl _
    · next hh =>
      cases hs : step piece.machine c with
      | none => simp [hs] at hr
      | some d =>
        cases ht : runFrom piece.machine fuel d with
        | none => simp [hs,ht] at hr
        | some tail =>
          simp only [hs,ht,Option.some.injEq] at hr
          subst r
          have hlocal : OrdinaryOracleStep o (ports.program piece) 1 c d :=
            OrdinaryOracleStep.local (program := ports.program piece) c d
              (by simpa [Ports.program] using hh) (hq c.control) hs
          simpa only [Nat.add_comm] using OrdinaryOracleTrace.cons hlocal (ih d tail ht)

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
