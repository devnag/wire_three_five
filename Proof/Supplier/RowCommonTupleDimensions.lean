import Proof.Supplier.RowCommonResources

/-! The common occurrence bound N*Q and output width w*N*Q are computed
from their actual retained unary drivers. The signed-field driver p+1 is
printed in precisely the CompareMachine representation of the row bank. -/
namespace NearCubicWires.RepairOrdinary.RowCommonTupleDimensions
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open RowCommonSize (put focus_put)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w N Q : ℕ) : RowCommonSize.Store := fun i=>
  if i=0 then List.replicate w true else if i=1 then UnaryTemplate.tape N
  else if i=2 then UnaryTemplate.tape Q else []
def data1 (w N Q : ℕ) := put (input w N Q) 3 4
  (List.replicate N true) (List.replicate (N+2) false)
def data2 (w N Q : ℕ) := put (data1 w N Q) 5 6
  (List.replicate (N*Q) true) (List.replicate (WilliamsUnaryProduct.scratch N Q) false)
def data3 (w N Q : ℕ) := put (data2 w N Q) 7 8
  (UnaryTemplate.tape (N*Q)) (List.replicate (N*Q+3) false)
def data4 (w N Q : ℕ) := put (data3 w N Q) 9 10
  (List.replicate (w*(N*Q)) true) (List.replicate (WilliamsUnaryProduct.scratch w (N*Q)) false)
def data5 (w N Q : ℕ) := put (data4 w N Q) 11 12
  (UnaryTemplate.tape (w*(N*Q))) (List.replicate (w*(N*Q)+3) false)
def output (w N Q : ℕ) := put (data5 w N Q) 13 14
  (CompareMachine.word (w*(N*Q)+1)) (List.replicate (w*(N*Q)+2) false)
def slots1 : Fin 3→Fin 17 := ![1,3,4]
def slots2 : Fin 4→Fin 17 := ![3,2,5,6]
def slots3 : Fin 3→Fin 17 := ![5,7,8]
def slots4 : Fin 4→Fin 17 := ![0,7,9,10]
def slots5 : Fin 3→Fin 17 := ![9,11,12]
def slots6 : Fin 3→Fin 17 := ![11,13,14]
noncomputable def phase1 := RecoveryFocus.machine slots1 (UWalkUnary.machine false false)
noncomputable def phase2 := RecoveryFocus.machine slots2 ClockUnaryProduct.machine
noncomputable def phase3 := RecoveryFocus.machine slots3 (DimensionTemplate.machine false)
noncomputable def phase4 := RecoveryFocus.machine slots4 ClockUnaryProduct.machine
noncomputable def phase5 := RecoveryFocus.machine slots5 (DimensionTemplate.machine false)
noncomputable def phase6 := RecoveryFocus.machine slots6 (UWalkUnary.machine true true)
noncomputable def first := Composition.machine phase1 phase2
noncomputable def second := Composition.machine first phase3
noncomputable def third := Composition.machine second phase4
noncomputable def fourth := Composition.machine third phase5
noncomputable def machine := Composition.machine fourth phase6
def budget (w N Q : ℕ) := (2*N+6)+WilliamsUnaryProduct.budget N Q+(2*(N*Q)+8)+
  WilliamsUnaryProduct.budget w (N*Q)+(2*(w*(N*Q))+8)+(2*(w*(N*Q))+6)+5



end NearCubicWires.RepairOrdinary.RowCommonTupleDimensions
