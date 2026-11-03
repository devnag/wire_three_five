import Proof.CaseAnalysis.RowsBankFields

/-! Between polynomial families, the exact 0/1 head pattern permits one
left step and the existing C sweep. The accumulated output is never scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsBankFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroHeads (out : List Bool) (i : Fin 113) := if i=31 then out.length else 0
def position (forward : Bool) : Machine 113 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if raised i then if forward then .right else .left else .stay⟩ else none

def work (i : Fin 110) : Fin 113 :=
  if i.val<31 then ⟨i.val,by omega⟩ else if i.val<103 then ⟨i.val+1,by omega⟩
  else ⟨i.val+3,by have h:=i.isLt; omega⟩

def slots : Fin 112→Fin 113 := Fin.addCases (m:=110) (n:=2) work ![104,105]

noncomputable def erase := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 110)
noncomputable def machine := Composition.machine (position false) erase
def budget (C : ℕ) := 2*C+6
def blank (C : ℕ) (out : List Bool) (i : Fin 113) :=
  if i=31 then out else if i=104 then List.replicate C true
  else if i=105 then List.replicate (C+1) false else List.replicate C false

end NearCubicWires.RepairOrdinary.CloseoutRowsBankClear
