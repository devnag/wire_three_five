import Proof.Amplification.RecoveryFormulaSerializePrepare

/-! The original balanced serializer is now callable on just its field
stream from literal external input and blank scratch. Its count is measured
by actual transitions, and its native head1 convention is physically set. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverHeads (i : Fin 131) := if i=3 then 1 else 0
def shift : Machine 131 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i=3 then .right else .stay⟩ else none

theorem shift_step (t : Fin 131→List Bool) :
    step shift (initialConfiguration shift t)=some ⟨1,driverHeads,t⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi:i=3 <;> simp [applyAction,shift,initialConfiguration,driverHeads,hi,HeadMove.apply]
  · rfl

theorem shift_run (t : Fin 131→List Bool) : ∃ r,
    run shift 1 t=some r ∧ r.final=(⟨1,driverHeads,t⟩ : Configuration 131 2) ∧ r.steps=1 :=
  (Timed.single (by rfl) (shift_step t)).run (by rfl)

theorem native_heads (i : Fin 128) : driverHeads (nativeSlots i)=PCPTraversal.heads 0 i := by
  have he : nativeSlots i=3 ↔ i=2 := by
    constructor
    · intro h; apply Fin.ext; have hv:=congrArg (fun j : Fin 131=>j.val) h; dsimp [nativeSlots] at hv; omega
    · rintro rfl; rfl
  simp only [driverHeads,he,PCPTraversal.heads]
  by_cases hi:i=0
  · subst i; rfl
  · simp [hi]

noncomputable def serializeMachine := RecoveryFocus.machine nativeSlots PCPTraversal.machine
noncomputable def tailMachine := Composition.machine shift serializeMachine
noncomputable def machine := Composition.machine prepareMachine tailMachine
def rawBudget (fields : List (List Bool)) := prepareBudget fields+1+(1+1+PCPTraversal.budget (mass fields))


end NearCubicWires.RepairSource.RecoveryFormulaSerialize
