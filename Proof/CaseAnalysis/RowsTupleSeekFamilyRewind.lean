import Proof.Amplification.RecoveryScratchErase
import Proof.CaseAnalysis.RowsTupleSeekDock
import Proof.CaseAnalysis.WitnessPaddedReset
import Proof.MachineModel.CacheRewind

/-! Family restart capacity D is separate from the per-term parser capacity
C. D pays only traversal of the actual three logical family streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem rewind_at {t : ℕ} (src driver log : Fin t) (hd : src≠driver) (hl : src≠log) (hdl : driver≠log)
    (D : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool) (hp : H src ≤ D)
    (hdh : H driver=0) (hlh : H log=0) (hda : A driver=List.replicate D true)
    (hla : A log=List.replicate (D+1) false) :
    Step (RecoveryFocus.machine ![src,driver,log] CompetitorRecordRewind.machine) (2*D+2)
      H A (Function.update H src 0) A := by
  apply dock_exact (CacheRewind.rewind_step (A src) D (H src) hp) ![src,driver,log]
    (by intro i j hij;fin_cases i <;> fin_cases j <;> simp_all)
  · intro i;fin_cases i <;> simp [hdh,hlh]
  · intro i;fin_cases i <;> simp [hda,hla]
  · intro i;fin_cases i <;> simp [hd.symm,hl.symm,hdh,hlh]
  · intro i;fin_cases i <;> simp [hda,hla]
  · intro i hi
    have hs : i≠src := (hi 0).symm
    simp [hs]


end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
