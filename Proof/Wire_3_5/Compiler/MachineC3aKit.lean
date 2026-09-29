import Proof.Wire_3_5.Compiler.MachineC3aDec

/-! # C3a machine, the stage kit: docking stages whose heads start and end at cell `0` (P3:1636-1664)

Paper: the pool builder is one deterministic construction, "Decompose an original-coordinate threshold using Lemma
alg:disjoint, and then substitute these coordinate functions" (P3:1636-1641), composed of stages. Every stage of C3a's
machine starts and ends with every head at cell `0` (masked resets), so a stage is a `Step` between banks with zero
heads, docked by an injective slot map. **`dockZ`**: docking such a stage into any layout; **`dockZL`**: into the left
part of `Fin (K + m)`; **`install_eval`**, **`dockH_eval`**: the docked bank and heads at a point; **`inst`**, **`dockZL'`**: the docked bank as a computable function, computed by a search over the slots (so a
concrete slot map is evaluated by `decide`/`simp`). The paper quantity is the composition of the pool builder's
stages. Main declarations: **`dockZ`**, **`dockZL`**, `slotOf`, **`install_eval`**, **`dockH_eval`**, `inst`, **`dockZL'`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

/-- **A zero-head stage, docked on the left part** of `Fin (K + m)`. -/
theorem dockZL {k K m s c : ℕ} {p : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step p c (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin k → Fin K) (hs : Function.Injective sl)
    (L : Fin K → List Bool) (R : Fin m → List Bool) (hL : ∀ j, L (sl j) = tin j) :
    Step (RecoveryFocus.machine (shiftL m sl) p) c (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) L R)
      (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) (install sl L tout) R) := by
  have e := dockRun_left h sl hs (fun _ => 0) L (fun _ => 0) R (fun _ => rfl) hL
  have hz : Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin K => 0) (fun _ : Fin m => 0) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [dockH_existing sl (fun _ => 0) (fun _ => 0) (fun _ => rfl), hz] at e
  exact e

/-- The slot hitting a point, by search. -/
def slotOf {t u : ℕ} (sl : Fin t → Fin u) (z : Fin u) : Option (Fin t) := (List.finRange t).find? fun j => sl j = z

theorem slotOf_some {t u : ℕ} (sl : Fin t → Fin u) (z : Fin u) (j : Fin t) (h : slotOf sl z = some j) : sl j = z := by
  have := List.find?_some h
  simpa using this

theorem slotOf_none {t u : ℕ} (sl : Fin t → Fin u) (z : Fin u) (h : slotOf sl z = none) : ∀ j, sl j ≠ z := by
  intro j hj
  have := List.find?_eq_none.mp h j (List.mem_finRange j)
  simp [hj] at this

/-- **The docked bank at a point**. -/
theorem install_eval {t u : ℕ} (sl : Fin t → Fin u) (hs : Function.Injective sl) (A : Fin u → List Bool)
    (v : Fin t → List Bool) (z : Fin u) :
    install sl A v z = match slotOf sl z with | some j => v j | none => A z := by
  cases h : slotOf sl z with
  | some j =>
    have := slotOf_some sl z j h
    subst this
    exact install_slot sl hs A v j
  | none => exact install_other sl A v z (slotOf_none sl z h)

/-- **The docked heads at a point**. -/
theorem dockH_eval {t u : ℕ} (sl : Fin t → Fin u) (hs : Function.Injective sl) (H : Fin u → ℕ) (v : Fin t → ℕ)
    (z : Fin u) : dockH sl H v z = match slotOf sl z with | some j => v j | none => H z := by
  cases h : slotOf sl z with
  | some j =>
    have := slotOf_some sl z j h
    subst this
    exact dockH_slot sl hs H v j
  | none => exact dockH_other sl H v z (slotOf_none sl z h)

/-- The docked bank as a computable function (`install` is defined through a classical search). -/
def inst {t u : ℕ} (sl : Fin t → Fin u) (A : Fin u → List Bool) (v : Fin t → List Bool) : Fin u → List Bool :=
  fun z => match slotOf sl z with | some j => v j | none => A z

theorem install_eq_inst {t u : ℕ} (sl : Fin t → Fin u) (hs : Function.Injective sl) (A : Fin u → List Bool)
    (v : Fin t → List Bool) : install sl A v = inst sl A v := funext (install_eval sl hs A v)

/-- **`dockZL` with the computable bank.** -/
theorem dockZL' {k K m s c : ℕ} {p : Machine k s} {tin tout : Fin k → List Bool}
    (h : Step p c (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin k → Fin K) (hs : Function.Injective sl)
    (L : Fin K → List Bool) (R : Fin m → List Bool) (hL : ∀ j, L (sl j) = tin j) :
    Step (RecoveryFocus.machine (shiftL m sl) p) c (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) L R)
      (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) (inst sl L tout) R) := by
  rw [← install_eq_inst sl hs]
  exact dockZL h sl hs L R hL

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit
