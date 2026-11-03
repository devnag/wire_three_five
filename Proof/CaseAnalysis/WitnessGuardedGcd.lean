import Proof.CaseAnalysis.WitnessRationalGuard
import Proof.Hierarchy.CompetitorGcdLoop

/-! One actual branch checks both original numeric fields before entering
the existing gcd loop. Rejected fields never execute that loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem gcd_ready (w a b c : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    ∃ t aa bb, t ≤ (a+b+1)*(32*w+40) ∧
      ReadyRun CompetitorGcd.machine t (CompetitorGcd.data w a b c false)
        (CompetitorGcd.data w aa bb (Nat.gcd a b) true) := by
  obtain ⟨t, aa, bb, ht, path⟩ := CompetitorGcd.loop w a b c false ha hb
  obtain ⟨r, hr, hf, hs⟩ := path.run (by
    change (RecoveryCalls.machine CompetitorGcd.sizes CompetitorGcd.programs 0 CompetitorGcd.next).halted
      (RecoveryCalls.stopped CompetitorGcd.sizes (fun _ => 0)
        (CompetitorGcd.data w aa bb (Nat.gcd a b) true)).control = true
    simp [RecoveryCalls.machine, RecoveryCalls.stopped])
  exact ⟨t, aa, bb, ht, r, hr,
    by simp [hf, CompetitorGcd.stopped, RecoveryCalls.stopped],
    by intro i; simp [hf, CompetitorGcd.stopped, RecoveryCalls.stopped], hs⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
