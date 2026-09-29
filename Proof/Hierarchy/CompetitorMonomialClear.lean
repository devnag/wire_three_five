import Proof.Hierarchy.CompetitorMonomialFields

/-! Two physical clears used by the scalar fold: the non-accumulator
workspace before each term, and the three old accumulator cells before
copyback. Both use the same retained unary driver and reset word. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {k : ℕ} (slot : Fin k → Fin 88) : Fin (k+2) → Fin 88 :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => Fin 88)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => Fin 88) slot (fun _ => 84)) (fun _ => 85)
def eraseInput {k : ℕ} (cap : ℕ) (backing : Fin k → List Bool) : Fin (k+2) → List Bool :=
  Fin.addCases (m := k+1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := k) (n := 1) (motive := fun _ => List Bool)
      backing (fun _ => List.replicate cap true)) (fun _ => List.replicate (cap+1) false)
noncomputable def clearProgram {k : ℕ} (slot : Fin k → Fin 88) :=
  RecoveryFocus.machine (extend slot) (RecoveryScratchErase.resetMachine k)

theorem extend_cases {k : ℕ} (slot : Fin k → Fin 88) (j : Fin (k+2)) :
    extend slot j=if h : j.val<k then slot ⟨j.val,h⟩ else if j.val=k then 84 else 85 := by
  refine Fin.addCases (m := k+1) (n := 1) ?_ ?_ j
  · intro i
    refine Fin.addCases (m := k) (n := 1) ?_ ?_ i
    · intro a
      simp [extend,a.isLt]
    · intro a
      fin_cases a
      simp [extend]
  · intro i
    fin_cases i
    simp [extend]

theorem extend_injective {k : ℕ} (slot : Fin k → Fin 88)
    (hi : Function.Injective slot) (h84 : ∀ j,slot j≠84) (h85 : ∀ j,slot j≠85) :
    Function.Injective (extend slot) := by
  intro i j h
  rw [extend_cases,extend_cases] at h
  split_ifs at h with hi' hj' hj90 hi90 hj' hj90
  · have he := hi h
    exact Fin.ext (congrArg (fun a : Fin k => a.val) he)
  · exact False.elim (h84 _ h)
  · exact False.elim (h85 _ h)
  · exact False.elim (h84 _ h.symm)
  · exact Fin.ext (by omega)
  · have hv := congrArg Fin.val h
    change (84 : ℕ)=85 at hv
    omega
  · exact False.elim (h85 _ h.symm)
  · have hv := congrArg Fin.val h
    change (85 : ℕ)=84 at hv
    omega
  · exact Fin.ext (by omega)

def workSlot (j : Fin 81) : Fin 88 :=
  if j.val<74 then ⟨j.val,by omega⟩ else if j.val<78 then ⟨j.val+1,by omega⟩
  else if j.val=78 then 80 else ⟨j.val+7,by omega⟩

theorem work_injective : Function.Injective workSlot := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [workSlot] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem work_avoids (j : Fin 81) (i : Fin 88)
    (hi : i=74 ∨ i=79 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85) : workSlot j≠i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [workSlot] at hv
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    split_ifs at hv <;> (try simp only at hv) <;> omega

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
