import Proof.Supplier.RowCommonTupleDimensions

/-! Add the actual degree Q to the native base width, including an empty
cache, and print the exact signed-field driver. All four calls are paid. -/
namespace NearCubicWires.ExtIncidence.NativeFieldWidth
open LocalBitMultitape RepairOrdinary
open RepairOrdinary.RecoveryRootRound
open RepairOrdinary.RowCommonSize (put focus_put)
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (u Q : ℕ) : RowCommonSize.Store:=fun i=>
  if i=0 then List.replicate u true else if i=1 then UnaryTemplate.tape Q else []
def data1 (u Q : ℕ):=put (input u Q) 2 3 (List.replicate Q true) (List.replicate (Q+2) false)
def data2 (u Q : ℕ):=put (data1 u Q) 4 5 (List.replicate (u+Q) true) (List.replicate (u+Q+2) false)
def data3 (u Q : ℕ):=put (data2 u Q) 6 7 (UnaryTemplate.tape (u+Q)) (List.replicate (u+Q+3) false)
def output (u Q : ℕ):=put (data3 u Q) 8 9 (CompareMachine.word (u+Q+1)) (List.replicate (u+Q+2) false)
def s1 : Fin 3→Fin 17:=![1,2,3]
def s2 : Fin 4→Fin 17:=![0,2,4,5]
def s3 : Fin 3→Fin 17:=![4,6,7]
def s4 : Fin 3→Fin 17:=![6,8,9]
noncomputable def phase1:=RecoveryFocus.machine s1 (UWalkUnary.machine false false)
noncomputable def phase2:=RecoveryFocus.machine s2 ClockUnarySum.machine
noncomputable def phase3:=RecoveryFocus.machine s3 (DimensionTemplate.machine false)
noncomputable def phase4:=RecoveryFocus.machine s4 (UWalkUnary.machine true true)
noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine phase1 phase2) phase3) phase4
def budget (u Q : ℕ):=2*Q+6*(u+Q)+29


end NearCubicWires.ExtIncidence.NativeFieldWidth
