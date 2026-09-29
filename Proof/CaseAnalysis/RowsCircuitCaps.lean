import Proof.CaseAnalysis.RowsCircuitCapCompare

/-! The two original circuit resource guards execute on the produced
small counters and retained policy caps. One final instruction writes the
circuit verdict; the measured-counter bound pays all private scratch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairSource.CloseoutSchedule CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def descriptionSlots (threshold : Bool) : Fin 6 → Fin 1703 :=
  ![if threshold then 653 else 649,1699,656,657,658,659]
def wireSlots : Fin 6 → Fin 1703 := ![660,1698,661,662,663,664]
def flagSlots : Fin 3 → Fin 1703 := ![658,663,1700]
noncomputable def description (threshold : Bool):=RecoveryFocus.machine (descriptionSlots threshold) RawCompare.machine
noncomputable def wires:=RecoveryFocus.machine wireSlots RawCompare.machine

def flagWorker : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some ⟨1,![none,none,some (bits 0 && bits 1)],fun _=>.stay⟩ else none
noncomputable def finish:=RecoveryFocus.machine flagSlots flagWorker
noncomputable def first (threshold : Bool):=Composition.machine (description threshold) wires
noncomputable def machine (threshold : Bool):=Composition.machine (first threshold) finish
def budget (desc wire L W : ℕ):=RawCompare.budget desc L+1+RawCompare.budget wire W+2

theorem flag_run (left right old : List Bool) : ClockJoin.ReadyRun flagWorker 1
    ![left,right,old] ![left,right,writeTapeBit old 0 (readTapeBit left 0 && readTapeBit right 0)]:=by
  let final:Configuration 3 2:=⟨1,fun _=>0,
    ![left,right,writeTapeBit old 0 (readTapeBit left 0 && readTapeBit right 0)]⟩
  have hs:step flagWorker (initialConfiguration flagWorker ![left,right,old])=some final:=by
    apply congrArg some;apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCaps
