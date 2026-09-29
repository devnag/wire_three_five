import Proof.CaseAnalysis.RowsEstimatorDriverCleanBank
import Proof.CaseAnalysis.RowsEstimatorScannedDriver

/-! Route the actual fresh driver bank into the checked copy/cleanup
consumer, retaining every original scanner port. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def count (a : WilliamsAlgorithm) := 98+2*DriverLayout.e a
noncomputable def tapes (a : WilliamsAlgorithm) := ScannedDriver.tapes a+3
noncomputable def old (a : WilliamsAlgorithm) (i : Fin (ScannedDriver.tapes a)) : Fin (tapes a) := i.castAdd 3
noncomputable def driver (a : WilliamsAlgorithm) : Fin (tapes a) := old a (ScannedDriver.driver a)
noncomputable def fresh (a : WilliamsAlgorithm) (i : Fin 3) : Fin (tapes a) := i.natAdd (ScannedDriver.tapes a)
noncomputable def work (a : WilliamsAlgorithm) (i : Fin (count a)) : Fin (tapes a) :=
  if i.val<97+2*DriverLayout.e a then ⟨70+i.val,by dsimp [tapes,ScannedDriver.tapes,DriverLayout.tapes,count] at *;omega⟩
  else ⟨70+i.val+1,by have hi:=i.isLt;dsimp [tapes,ScannedDriver.tapes,DriverLayout.tapes,count] at *;omega⟩
noncomputable def slots (a : WilliamsAlgorithm) : Fin (4+count a) → Fin (tapes a) :=
  Fin.addCases (![driver a,fresh a 0,fresh a 1,fresh a 2] : Fin 4 → Fin (tapes a)) (work a)


noncomputable def first (a : WilliamsAlgorithm) :=
  ClockJoin.lifted (Equiv.refl (Fin (tapes a))) (ScannedDriver.machine a)
noncomputable def last (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a)
  (DriverCleanBank.machine (count a) (DriverLayout.sweepCount a))
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (first a) (last a)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
