import Proof.Amplification.RecoveryPrefixOutputCall

/-! Whole ordinary-oracle canonical prefix search from the literal external
framed request and blank tapes. Every query, capacity allocation, driver move,
copy and return is included in its run. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixBody RecoveryQuery CanonicalSATSelfReduction CanonicalRecoveryLanguage CanonicalBinary TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem whole_ready (C payload total : Nat) (flat : Bool) (hC : 1073741824≤C) :
    ∃ cost ≤ budget C payload total,∃ out,
      Ready RecoveryOracle.correctedSat (program C flat) cost (input payload total) out ∧
      out 386=frame (search flat payload total []) := by
  obtain ⟨c0,hc0,h0⟩ := ordinary_ready (o:=RecoveryOracle.correctedSat) ports unwrap _ _ (unwrap_ready payload total)
  obtain ⟨prepared,hp,hprepared⟩ := prepare_ready C payload total hC
  obtain ⟨c1,hc1,h1⟩ := ordinary_ready (o:=RecoveryOracle.correctedSat) ports (prepare C) _ _ hp
  obtain ⟨c2,hc2,searched,h2,hsearched⟩ := loop_ready flat C payload total prepared hC hprepared
  obtain ⟨sealedOut,hs,hsealed⟩ := seal_ready _ total (search flat payload total []) searched hsearched
  obtain ⟨c3,hc3,h3⟩ := ordinary_ready (o:=RecoveryOracle.correctedSat) ports sealProgram _ _ hs
  obtain ⟨out,ho,hout⟩ := output_ready _ total (search flat payload total []) sealedOut (by simp) hsealed
  obtain ⟨c4,hc4,h4⟩ := ordinary_ready (o:=RecoveryOracle.correctedSat) ports output _ _ ho
  have hp0 := Ready.call ports (pieces C flat) 0 (next C flat) 0 1 h0 (by intro q; rfl)
  have hp1 := Ready.call ports (pieces C flat) 0 (next C flat) 1 2 h1 (by intro q; rfl)
  have hp2 := Ready.call ports (pieces C flat) 0 (next C flat) 2 3 h2 (by intro q; rfl)
  have hp3 := Ready.call ports (pieces C flat) 0 (next C flat) 3 4 h3 (by intro q; rfl)
  have hp4 := Ready.stop ports (pieces C flat) 0 (next C flat) 4 h4 (by intro q; rfl)
  have hwhole := trans hp0 (trans hp1 (trans hp2 (trans hp3 hp4)))
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces C flat j).states) 0)
      (initialConfiguration (pieces C flat 0).machine (input payload total))=
      initialConfiguration (program C flat).base.machine (input payload total) := rfl
  rw [hstart] at hwhole
  refine ⟨(c0+1)+((c1+1)+((c2+1)+((c3+1)+(c4+1)))),?_,out,?_,hout⟩
  · dsimp only [budget]
    omega
  · refine ⟨_,hwhole,?_,fun _=>rfl,rfl⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]

end NearCubicWires.RepairSource.RecoveryPrefixCold
