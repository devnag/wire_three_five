import Proof.Packets.SubstitutionOuterLoop
import Proof.Amplification.RecoveryScratchErase

/-! Physically allocate or clear all nine substitution scratch tapes35..43.
The atom bank34, arithmetic arena, raw reserve, and reset log are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScratch
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def slots : Fin 11→Fin 44 := Fin.addCases (m:=9) (n:=2) (fun j=>j.natAdd 35) ![32,33]
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 9)


end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionScratch
