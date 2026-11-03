import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidOwnedWarmJoin

/-! Actual retirement and the mandatory scanner preserve complete ownership. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem retire_owned_join {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (row : EquationRow.Input) (C D fuel bound : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) (worker : Machine (tapes a p) s)
    (initial : Configuration (tapes a p) s)
    (hr : WarmOwned a p worker fuel bound initial row C D word fields) :
    Owned a p (Composition.machine worker (retire a p)) (fuel+1+(2*D+4))
      (bound+1+(2*D+4)) (Composition.leftConfig 5 initial) row C D word fields := by
  obtain ⟨A,extra,x,hx,xh,xt,xs,props,xd,priv,protectedWords⟩:=hr
  obtain ⟨y,hy,yh,yt,ys⟩:=retire_run a p D word A extra props.2.2.1 xd
  have hc : Composition.restart x.final (retire a p).start=
      (⟨DriverRetire.machine.start,heads a p word,Fin.addCases A extra⟩ : Configuration (tapes a p) 5) :=
    restart_state x.final _ _ _ xh xt
  rw [←hc] at hy
  have hj:=Composition.run_join worker (retire a p) _ _ _ x y hx hy
  refine ⟨A,extra,Composition.joinedReceipt x y,hj,yh,yt,?_,props,priv,protectedWords⟩
  change x.steps+1+y.steps ≤ bound+1+(2*D+4)
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
