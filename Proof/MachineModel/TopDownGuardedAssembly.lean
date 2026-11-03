import Proof.MachineModel.TopDownWorkspaceGuardedWorker

/-! Coherent guarded endpoint cut. All finite-program choices remain data;
the three substantive regions are the actual admission receipt, admitted
Verdict, and Runtime of precisely the chosen gated worker. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.GuardedAssembly
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open WorkspaceGuardedWorker
noncomputable section

structure ProgramData where
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  coldCutoff : Nat
  baseOnset : Nat
  tapes : Nat
  admissionStates : Nat
  bodyStates : Nat
  admission : LocalBitMultitape.Machine tapes admissionStates
  continuation : LocalBitMultitape.Machine tapes bodyStates
  inputTape : Fin tapes
  lengthFlag : Fin tapes
  admissionFlag : Fin tapes
  result : Fin tapes
  preFuel : Nat → Nat
  bodyFuel : Nat → Nat

end
end NearCubicWires.P1TopDown.GuardedAssembly
