import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # C6 front: loops by invariant, and docking steps at explicit ambient banks

The front's loops (the atom decoders, U1b; the table writer, U5) run a body machine whose rounds are known only up to
an invariant (a round's private scratch is existential), so the loop is proved by invariant rather than along explicit
banks (`whileRun`): **`whileInv`**. And the rounds are compositions of stages docked at slot maps of one ambient
bank with nonzero heads: **`Step.dockAt`** (base `Step.focus` at an ambient bank that already holds the stage's entry).
Paper quantity: none (machine plumbing for the front's loops). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

variable {t s : ℕ}

/-- **A loop by invariant**: `n` rounds, each from an `Inv j` bank with the condition set to an `Inv (j+1)` bank in
`c` steps, the condition clear at `Inv n`. -/
theorem whileInv (M : Machine t s) (i : Fin t) (n c : ℕ) (Inv : ℕ → (Fin t → ℕ) → (Fin t → List Bool) → Prop)
    (hstep : ∀ j < n, ∀ H A, Inv j H A → ∃ H' A', Step M c H A H' A' ∧ Inv (j + 1) H' A')
    (hT : ∀ j < n, ∀ H A, Inv j H A → readTapeBit (A i) (H i) = true)
    (hF : ∀ H A, Inv n H A → readTapeBit (A i) (H i) = false)
    (H0 : Fin t → ℕ) (A0 : Fin t → List Bool) (h0 : Inv 0 H0 A0) :
    ∃ Hn An, Step (StreamController.machine M i) (n * (c + 2) + 1) H0 A0 Hn An ∧ Inv n Hn An := by
  have key : ∀ m j, j + m = n → ∀ H A, Inv j H A →
      ∃ Hn An, Step (StreamController.machine M i) (m * (c + 2) + 1) H A Hn An ∧ Inv n Hn An := by
    intro m
    induction m with
    | zero =>
      intro j hj H A hI
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨H, A, by simpa using whileF M i H A (hF H A hI), hI⟩
    | succ m ih =>
      intro j hj H A hI
      obtain ⟨H1, A1, h1, hI1⟩ := hstep j (by omega) H A hI
      obtain ⟨Hn, An, h2, hIn⟩ := ih (j + 1) (by omega) H1 A1 hI1
      exact ⟨Hn, An, (whileT M i (hT j (by omega) H A hI) h1 h2).enlarge (by nlinarith), hIn⟩
  exact key n 0 (by omega) H0 A0 h0

/-- Docking the ambient heads that already hold the stage's heads changes nothing. -/
theorem dockH_self {u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (H : Fin u → ℕ)
    (h : Fin t → ℕ) (hH : ∀ j, H (slots j) = h j) : dockH slots H h = H := by
  funext x
  by_cases hx : ∃ j, slots j = x
  · obtain ⟨j, rfl⟩ := hx; rw [dockH_slot slots hi, hH]
  · exact dockH_other slots H h x (fun j hj => hx ⟨j, hj⟩)

/-- Installing the tapes the ambient bank already holds changes nothing. -/
theorem install_self' {u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (a : Fin t → List Bool) (hA : ∀ j, A (slots j) = a j) : install slots A a = A := by
  funext x
  by_cases hx : ∃ j, slots j = x
  · obtain ⟨j, rfl⟩ := hx; rw [install_slot _ hi, hA]
  · exact install_other _ _ _ _ (fun j hj => hx ⟨j, hj⟩)

/-- **A stage docked at an ambient bank holding its entry**: the ambient bank after the stage is the stage's exit
installed at its slots, everything else unchanged. -/
theorem Step.dockAt {u : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have := Step.focus h slots hi H A
  rwa [dockH_self slots hi H hin hH, install_self' slots hi A tin hA] at this

/-- A ready run is a step between zero heads. -/
theorem step_of_ready {p : Machine t s} {n : ℕ} {A A' : Fin t → List Bool} (h : ClockJoin.ReadyRun p n A A') :
    Step p n (fun _ => 0) A (fun _ => 0) A' := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  exact ⟨r, hr, funext hh, ht, hs⟩

/-- A root-round ready run (exact time) is a step between zero heads. -/
theorem step_of_rready {p : Machine t s} {n : ℕ} {A A' : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p n A A') : Step p n (fun _ => 0) A (fun _ => 0) A' := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  exact ⟨r, hr, funext hh, ht, hs.le⟩


end NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
