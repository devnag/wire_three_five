import Proof.CaseAnalysis.RowsEstimatorScanRun

/-! Produce the scanner's field-count template from the actual retained
raw d and parity bit using the existing paid dimension/count workers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Fields
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ds : Fin 3→Fin 10:=![0,2,3]
def ws : Fin 4→Fin 10:=![2,1,4,5]
def us : Fin 3→Fin 10:=![4,6,7]
def ns : Fin 3→Fin 10:=![6,8,9]
def w (d : ℕ) (odd : Bool):=2*d-odd.toNat

def input (d : ℕ) (odd : Bool) : Fin 10→List Bool:=
  ![List.replicate d true,[odd],[],[],[],[],[],[],[],[]]
def a1 (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=2 then UnaryTemplate.tape d else if i=3 then List.replicate (d+3) false else input d odd i
def a2 (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=4 then CompareMachine.word (w d odd)
  else if i=5 then List.replicate (EquationWeightCount.ticks d odd) false else a1 d odd i
def a3 (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=6 then List.replicate (w d odd+1) true
  else if i=7 then List.replicate (w d odd+2) false else a2 d odd i
def output (d : ℕ) (odd : Bool) (i : Fin 10) : List Bool:=
  if i=8 then UnaryTemplate.tape (w d odd+2)
  else if i=9 then List.replicate (w d odd+4) false else a3 d odd i

noncomputable def first:=RecoveryFocus.machine ds (DimensionTemplate.machine false)
noncomputable def second:=RecoveryFocus.machine ws EquationWeightCount.machine
noncomputable def third:=RecoveryFocus.machine us (UWalkUnary.machine false true)
noncomputable def fourth:=RecoveryFocus.machine ns (DimensionTemplate.machine true)
noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine first second) third) fourth
def budget (d : ℕ) (odd : Bool):=6*d+4*w d odd+33

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Fields
