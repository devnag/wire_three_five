import Proof.Wire_3_5.Compiler.MachinePoolContract2

/-! # C3a machine, the layout: the pool builder's tapes, then the decomposition's (P3:1636-1641)

Paper: "Decompose an original-coordinate threshold using Lemma alg:disjoint, and then substitute these coordinate
functions" (P3:1636-1641). C3a's machine works on `Fin (K + m)`: its own `K` tapes first (the input on tape 0), then the
`m = CT a + 1` tapes of base's decomposition loop, a number depending on the decomposition algorithm. Machines of the
pool builder are docked on the left part (`shiftL`, **`install_left`**, **`dockH_left`**, **`dockRun_left`**). The
decomposition is docked on the right part except its ports (the request stream, the three outputs, the driver and the
templates), which live on the left part where the loads write them and the pool builder reads them (`portsL`,
**`install_ports`**, **`dockH_ports`**, **`dockRun_ports`**). The paper quantity is the pool builder's layout beside
the decomposition's. Main declarations: `shiftL`, **`install_left`**, **`dockH_left`**, **`dockRun_left`**, `portsL`,
**`install_ports`**, **`dockH_ports`**, **`dockRun_ports`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound

/-! ## The left part -/

/-- A slot map on the left part of a layout `Fin (K + m)`. -/
def shiftL {k K : ℕ} (m : ℕ) (s : Fin k → Fin K) : Fin k → Fin (K + m) := fun j => Fin.castAdd m (s j)

theorem shiftL_inj {k K : ℕ} (m : ℕ) (s : Fin k → Fin K) (hs : Function.Injective s) :
    Function.Injective (shiftL m s) := by
  intro i j h
  apply hs
  have := congrArg Fin.val h
  simp only [shiftL, Fin.val_castAdd] at this
  exact Fin.ext this

/-- **Installing on the left part** changes only the left part. -/
theorem install_left {k K m : ℕ} (s : Fin k → Fin K) (hs : Function.Injective s) (A : Fin K → List Bool)
    (B : Fin m → List Bool) (v : Fin k → List Bool) :
    install (shiftL m s) (Fin.addCases A B) v = Fin.addCases (install s A v) B := by
  classical
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.addCases_left]
    by_cases h : ∃ j, s j = i
    · obtain ⟨j, rfl⟩ := h
      have e1 := install_slot (shiftL m s) (shiftL_inj m s hs) (Fin.addCases A B) v j
      rw [install_slot s hs A v j]
      exact e1
    · push Not at h
      rw [install_other _ _ _ _ (fun j hj => by
        have := congrArg Fin.val hj
        simp only [shiftL, Fin.val_castAdd] at this
        exact h j (Fin.ext this)), install_other _ _ _ _ h, Fin.addCases_left]
  · rw [Fin.addCases_right]
    rw [install_other _ _ _ _ (fun j h => by
      have := congrArg Fin.val h
      simp only [shiftL, Fin.val_natAdd, Fin.val_castAdd] at this
      omega)]
    rw [Fin.addCases_right]

/-- **The heads on the left part** change only on the left part. -/
theorem dockH_left {k K m : ℕ} (s : Fin k → Fin K) (hs : Function.Injective s) (G : Fin K → ℕ) (H : Fin m → ℕ)
    (v : Fin k → ℕ) :
    dockH (shiftL m s) (Fin.addCases G H) v = Fin.addCases (dockH s G v) H := by
  classical
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.addCases_left]
    by_cases h : ∃ j, s j = i
    · obtain ⟨j, rfl⟩ := h
      have e1 := dockH_slot (shiftL m s) (shiftL_inj m s hs) (Fin.addCases G H) v j
      rw [dockH_slot s hs G v j]
      exact e1
    · push Not at h
      rw [dockH_other _ _ _ _ (fun j hj => by
        have := congrArg Fin.val hj
        simp only [shiftL, Fin.val_castAdd] at this
        exact h j (Fin.ext this)), dockH_other _ _ _ _ h, Fin.addCases_left]
  · rw [Fin.addCases_right]
    rw [dockH_other _ _ _ _ (fun j h => by
      have := congrArg Fin.val h
      simp only [shiftL, Fin.val_natAdd, Fin.val_castAdd] at this
      omega)]
    rw [Fin.addCases_right]

/-- **A step docked on the left part**, the right part unchanged. -/
theorem dockRun_left {k K m s n : ℕ} {p : Machine k s} {hin hout : Fin k → ℕ} {tin tout : Fin k → List Bool}
    (h : Step p n hin tin hout tout) (sl : Fin k → Fin K) (hs : Function.Injective sl) (G : Fin K → ℕ)
    (A : Fin K → List Bool) (HR : Fin m → ℕ) (AR : Fin m → List Bool) (hG : ∀ j, G (sl j) = hin j)
    (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine (shiftL m sl) p) n (Fin.addCases G HR) (Fin.addCases A AR)
      (Fin.addCases (dockH sl G hout) HR) (Fin.addCases (install sl A tout) AR) := by
  have e := GF2.dockRun h (shiftL m sl) (shiftL_inj m sl hs) (Fin.addCases G HR) (Fin.addCases A AR)
    (fun j => by simp only [shiftL, Fin.addCases_left]; exact hG j)
    (fun j => by simp only [shiftL, Fin.addCases_left]; exact hA j)
  rw [install_left sl hs, dockH_left sl hs] at e
  exact e

/-! ## A right-part machine with ports on the left part -/

/-- The slot map of a machine on `Fin m` placed on the right part of `Fin (K + m)`, except its ports `P i`, which go
to `q i` on the left part. -/
noncomputable def portsL {k K m : ℕ} (P : Fin k → Fin m) (q : Fin k → Fin K) : Fin m → Fin (K + m) := fun j =>
  if h : ∃ i, P i = j then Fin.castAdd m (q (Classical.choose h)) else Fin.natAdd K j

theorem portsL_port {k K m : ℕ} (P : Fin k → Fin m) (q : Fin k → Fin K) (hP : Function.Injective P) (i : Fin k) :
    portsL P q (P i) = Fin.castAdd m (q i) := by
  have h : ∃ i', P i' = P i := ⟨i, rfl⟩
  simp only [portsL, dif_pos h]
  rw [hP (Classical.choose_spec h)]

theorem portsL_other {k K m : ℕ} (P : Fin k → Fin m) (q : Fin k → Fin K) (j : Fin m) (h : ¬ ∃ i, P i = j) :
    portsL P q j = Fin.natAdd K j := by
  simp only [portsL, dif_neg h]

theorem portsL_inj {k K m : ℕ} (P : Fin k → Fin m) (q : Fin k → Fin K) (hP : Function.Injective P)
    (hq : Function.Injective q) : Function.Injective (portsL P q) := by
  classical
  intro x y hxy
  by_cases hx : ∃ i, P i = x
  · obtain ⟨i, rfl⟩ := hx
    by_cases hy : ∃ i, P i = y
    · obtain ⟨j, rfl⟩ := hy
      rw [portsL_port P q hP, portsL_port P q hP] at hxy
      have := congrArg Fin.val hxy
      simp only [Fin.val_castAdd] at this
      rw [hq (Fin.ext this)]
    · rw [portsL_port P q hP, portsL_other P q y hy] at hxy
      have := congrArg Fin.val hxy
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  · by_cases hy : ∃ i, P i = y
    · obtain ⟨j, rfl⟩ := hy
      rw [portsL_other P q x hx, portsL_port P q hP] at hxy
      have := congrArg Fin.val hxy
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rw [portsL_other P q x hx, portsL_other P q y hy] at hxy
      have := congrArg Fin.val hxy
      simp only [Fin.val_natAdd] at this
      exact Fin.ext (by omega)

/-- **Installing through the ports map**: the ports' contents go to the left part, the other tapes to the right. -/
theorem install_ports {k K m : ℕ} (P : Fin k → Fin m) (q : Fin k → Fin K) (hP : Function.Injective P)
    (hq : Function.Injective q) (A : Fin K → List Bool) (B : Fin m → List Bool) (v : Fin m → List Bool) :
    install (portsL P q) (Fin.addCases A B) v =
      Fin.addCases (install q A (fun i => v (P i))) (fun j => if ∃ i, P i = j then B j else v j) := by
  classical
  have hinj := portsL_inj P q hP hq
  funext x
  refine Fin.addCases (fun y => ?_) (fun j => ?_) x
  · rw [Fin.addCases_left]
    by_cases hy : ∃ i, q i = y
    · obtain ⟨i, rfl⟩ := hy
      rw [install_slot q hq A _ i]
      have e := install_slot (portsL P q) hinj (Fin.addCases A B) v (P i)
      rw [portsL_port P q hP] at e
      exact e
    · push Not at hy
      rw [install_other q A _ y hy]
      rw [install_other _ _ _ _ (fun j hj => by
        by_cases hp : ∃ i, P i = j
        · obtain ⟨i, rfl⟩ := hp
          rw [portsL_port P q hP] at hj
          have := congrArg Fin.val hj
          simp only [Fin.val_castAdd] at this
          exact hy i (Fin.ext this)
        · rw [portsL_other P q j hp] at hj
          have := congrArg Fin.val hj
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := y.isLt
          omega)]
      rw [Fin.addCases_left]
  · rw [Fin.addCases_right]
    by_cases hp : ∃ i, P i = j
    · rw [if_pos hp]
      rw [install_other _ _ _ _ (fun j' hj' => by
        by_cases hp' : ∃ i, P i = j'
        · obtain ⟨i, rfl⟩ := hp'
          rw [portsL_port P q hP] at hj'
          have := congrArg Fin.val hj'
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := (q i).isLt
          omega
        · rw [portsL_other P q j' hp'] at hj'
          have := congrArg Fin.val hj'
          simp only [Fin.val_natAdd] at this
          obtain ⟨i, hi⟩ := hp
          exact hp' ⟨i, hi.trans (Fin.ext (by omega))⟩)]
      rw [Fin.addCases_right]
    · rw [if_neg hp]
      have e := install_slot (portsL P q) hinj (Fin.addCases A B) v j
      rw [portsL_other P q j hp] at e
      exact e

/-- **The heads through the ports map**. -/
theorem dockH_ports {k K m : ℕ} (P : Fin k → Fin m) (q : Fin k → Fin K) (hP : Function.Injective P)
    (hq : Function.Injective q) (G : Fin K → ℕ) (H : Fin m → ℕ) (v : Fin m → ℕ) :
    dockH (portsL P q) (Fin.addCases G H) v =
      Fin.addCases (dockH q G (fun i => v (P i))) (fun j => if ∃ i, P i = j then H j else v j) := by
  classical
  have hinj := portsL_inj P q hP hq
  funext x
  refine Fin.addCases (fun y => ?_) (fun j => ?_) x
  · rw [Fin.addCases_left]
    by_cases hy : ∃ i, q i = y
    · obtain ⟨i, rfl⟩ := hy
      rw [dockH_slot q hq G _ i]
      have e := dockH_slot (portsL P q) hinj (Fin.addCases G H) v (P i)
      rw [portsL_port P q hP] at e
      exact e
    · push Not at hy
      rw [dockH_other q G _ y hy]
      rw [dockH_other _ _ _ _ (fun j hj => by
        by_cases hp : ∃ i, P i = j
        · obtain ⟨i, rfl⟩ := hp
          rw [portsL_port P q hP] at hj
          have := congrArg Fin.val hj
          simp only [Fin.val_castAdd] at this
          exact hy i (Fin.ext this)
        · rw [portsL_other P q j hp] at hj
          have := congrArg Fin.val hj
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := y.isLt
          omega)]
      rw [Fin.addCases_left]
  · rw [Fin.addCases_right]
    by_cases hp : ∃ i, P i = j
    · rw [if_pos hp]
      rw [dockH_other _ _ _ _ (fun j' hj' => by
        by_cases hp' : ∃ i, P i = j'
        · obtain ⟨i, rfl⟩ := hp'
          rw [portsL_port P q hP] at hj'
          have := congrArg Fin.val hj'
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          have := (q i).isLt
          omega
        · rw [portsL_other P q j' hp'] at hj'
          have := congrArg Fin.val hj'
          simp only [Fin.val_natAdd] at this
          obtain ⟨i, hi⟩ := hp
          exact hp' ⟨i, hi.trans (Fin.ext (by omega))⟩)]
      rw [Fin.addCases_right]
    · rw [if_neg hp]
      have e := dockH_slot (portsL P q) hinj (Fin.addCases G H) v j
      rw [portsL_other P q j hp] at e
      exact e

/-- **A right-part machine with left ports**, docked. -/
theorem dockRun_ports {k K m s n : ℕ} {p : Machine m s} {hin hout : Fin m → ℕ} {tin tout : Fin m → List Bool}
    (h : Step p n hin tin hout tout) (P : Fin k → Fin m) (q : Fin k → Fin K) (hP : Function.Injective P)
    (hq : Function.Injective q) (G : Fin K → ℕ) (A : Fin K → List Bool) (HR : Fin m → ℕ) (AR : Fin m → List Bool)
    (hG : ∀ i, G (q i) = hin (P i)) (hA : ∀ i, A (q i) = tin (P i))
    (hHR : ∀ j, (¬ ∃ i, P i = j) → HR j = hin j) (hAR : ∀ j, (¬ ∃ i, P i = j) → AR j = tin j) :
    Step (RecoveryFocus.machine (portsL P q) p) n (Fin.addCases G HR) (Fin.addCases A AR)
      (Fin.addCases (dockH q G (fun i => hout (P i))) (fun j => if ∃ i, P i = j then HR j else hout j))
      (Fin.addCases (install q A (fun i => tout (P i))) (fun j => if ∃ i, P i = j then AR j else tout j)) := by
  classical
  have e := GF2.dockRun h (portsL P q) (portsL_inj P q hP hq) (Fin.addCases G HR) (Fin.addCases A AR)
    (fun j => by
      by_cases hp : ∃ i, P i = j
      · obtain ⟨i, rfl⟩ := hp
        rw [portsL_port P q hP, Fin.addCases_left]; exact hG i
      · rw [portsL_other P q j hp, Fin.addCases_right]; exact hHR j hp)
    (fun j => by
      by_cases hp : ∃ i, P i = j
      · obtain ⟨i, rfl⟩ := hp
        rw [portsL_port P q hP, Fin.addCases_left]; exact hA i
      · rw [portsL_other P q j hp, Fin.addCases_right]; exact hAR j hp)
  rw [install_ports P q hP hq, dockH_ports P q hP hq] at e
  exact e


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
