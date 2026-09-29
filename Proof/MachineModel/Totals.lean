import Proof.MachineModel.Basic

/-! P25: the two count workers.

`TotalsAppend` walks one child-count template (`UnaryTemplate.tape count`, head 1)
and appends `count` marks to the growing total tape, then returns the template
head to 1. `FinalizeT` turns the accumulated total `false :: 1^B` into the exact
`UnaryTemplate.tape B` at head 1 and allocates the incidence scratch
`replicate B false` at head 0, walking the template three times. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace TotalsAppend

/-- Tape 0 count template, tape 1 total. States: 0 walk, 1 return, 2 halt. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨0, ![none, some true], ![.right, .right]⟩
      else ⟨1, fun _ => none, ![.left, .stay]⟩)
    else if q.val = 1 then some (if bits 0 then ⟨1, fun _ => none, ![.left, .stay]⟩
      else ⟨2, fun _ => none, ![.right, .stay]⟩)
    else none

def cfg (q : Fin 3) (count ch : ℕ) (t : List Bool) : Configuration 2 3 :=
  ⟨q, ![ch, t.length], ![UnaryTemplate.tape count, t]⟩

@[simp] theorem halted_two : machine.halted 2 = true := rfl

theorem walk_step (count k : ℕ) (hk : k < count) (t : List Bool) :
    step machine (cfg 0 count (k+1) t) = some (cfg 0 count (k+2) (t ++ [true])) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark count k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end]

theorem walk_end (count : ℕ) (t : List Bool) :
    step machine (cfg 0 count (count+1) t) = some (cfg 1 count count t) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back_step (count k : ℕ) (hk : k < count) (t : List Bool) :
    step machine (cfg 1 count (k+1) t) = some (cfg 1 count k t) := by
  simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_mark count k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back_stop (count : ℕ) (t : List Bool) :
    step machine (cfg 1 count 0 t) = some (cfg 2 count 1 t) := by
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem walk_timed (count k r : ℕ) (hkr : k + r = count) (t : List Bool) :
    Timed machine r (cfg 0 count (k+1) (t ++ List.replicate k true))
      (cfg 0 count (count+1) (t ++ List.replicate count true)) := by
  induction r generalizing k with
  | zero =>
    have : k = count := by omega
    subst this; exact Timed.refl machine _
  | succ r ih =>
    have h1 := walk_step count k (by omega) (t ++ List.replicate k true)
    rw [List.append_assoc, ← List.replicate_succ'] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ih (k+1) (by omega))
    have e : 1 + r = r + 1 := Nat.add_comm 1 r
    rw [e] at h; exact h

theorem back_timed (count k : ℕ) (hk : k ≤ count) (t : List Bool) :
    Timed machine (k+1) (cfg 1 count k t) (cfg 2 count 1 t) := by
  induction k with
  | zero => exact Timed.single (by rfl) (back_stop count t)
  | succ k ih =>
    have h := (Timed.single (p := machine) (by rfl) (back_step count k (by omega) t)).trans (ih (by omega))
    have e : 1 + (k+1) = k+1+1 := by omega
    rw [e] at h; exact h

theorem append_run (count : ℕ) (t : List Bool) :
    ∃ r : ExecutionReceipt 2 3, runFrom machine (2*count+2) (cfg 0 count 1 t) = some r ∧
      r.final = cfg 2 count 1 (t ++ List.replicate count true) ∧ r.steps = 2*count+2 := by
  have s1 := walk_timed count 0 count (by omega) t
  simp only [List.replicate_zero, List.append_nil] at s1
  have s2 := Timed.single (p := machine) (by rfl) (walk_end count (t ++ List.replicate count true))
  have s3 := back_timed count count le_rfl (t ++ List.replicate count true)
  have h := (s1.trans s2).trans s3
  have e : count + 1 + (count+1) = 2*count+2 := by omega
  rw [e] at h
  exact h.run rfl

end TotalsAppend

namespace FinalizeT

/-- Tape 0 total/template, tape 1 incidence scratch. States: 0 terminator, 1 back
appending scratch zeros, 2 forward returning the scratch head, 3 back to the mark, 4 halt. -/
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then some ⟨1, ![some false, none], ![.left, .stay]⟩
    else if q.val = 1 then some (if bits 0 then ⟨1, ![none, some false], ![.left, .right]⟩
      else ⟨2, fun _ => none, ![.right, .stay]⟩)
    else if q.val = 2 then some (if bits 0 then ⟨2, fun _ => none, ![.right, .left]⟩
      else ⟨3, fun _ => none, ![.left, .stay]⟩)
    else if q.val = 3 then some (if bits 0 then ⟨3, fun _ => none, ![.left, .stay]⟩
      else ⟨4, fun _ => none, ![.right, .stay]⟩)
    else none

@[simp] theorem halted_four : machine.halted 4 = true := rfl

end FinalizeT

end NearCubicWires.ExtDecompositionBatch
