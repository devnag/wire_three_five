import Proof.Wire_3_5.Primitive.Writers.CellLoop

/-! # PA (d), the writer shell, part 1: the shell's layout and its bookkeeping

The writers' shell (the shared WRITER-SHELL kit: inBank → the scrubbed loop entry → the loop → a masked reset →
`WriterRun`) runs on ONE layout: the cell of the unit machine (`CellLoop.TT x` tapes), the scrub entry's calc
workspace (`Scrub.wk D`), the scrub's log and driver, the loop counter, and the tapes of the polynomial run that
computes the loop bound (`UnaryCalc.tapes D1`). This module names the tapes (`cT`, `wT`, `lgT`, `drT`, `kT`, `eT`),
decomposes a bank into its regions (**`regions`**), and gives the generic facts the stages use:

* `install_eq`, `dockH_eq`: a docked run's exit bank, pointwise;
* **`Step.len`**: a run of `n` steps leaves every tape of length at most `k + n` if it started within `k`
  (base `DecompositionSource.one_tape_support`);
* `ready_of_step`: an all-heads-zero `Step` is a `ClockJoin.ReadyRun`.

Paper quantity: none (machine plumbing for the writers, whose types carry the paper's tapes). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Shell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop

section Tapes



end Tapes

/-! ## Docked runs, lengths, ready runs -/

theorem install_eq {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (L : Fin t → List Bool) (B : Fin u → List Bool) (h1 : ∀ j, B (slots j) = L j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) : install slots A L = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [install_slot _ hi]
    exact (h1 j).symm
  · have hn : ∀ j, slots j ≠ i := fun j e => h ⟨j, e⟩
    rw [install_other _ _ _ _ hn]
    exact (h2 i hn).symm

theorem dockH_eq {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → ℕ)
    (L : Fin t → ℕ) (B : Fin u → ℕ) (h1 : ∀ j, B (slots j) = L j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) : dockH slots A L = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [dockH_slot _ hi]
    exact (h1 j).symm
  · have hn : ∀ j, slots j ≠ i := fun j e => h ⟨j, e⟩
    rw [dockH_other _ _ _ _ hn]
    exact (h2 i hn).symm

/-- **A run's tapes grow by at most its steps.** -/
theorem Step.len {t s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (i : Fin t) (k : ℕ) (hh : hin i ≤ k) (ht : (tin i).length ≤ k) :
    (tout i).length ≤ k + n := by
  obtain ⟨r, hr, _, hT, hs⟩ := h
  have := DecompositionSource.one_tape_support p n ⟨p.start, hin, tin⟩ r i k hr hh ht
  rw [hT] at this
  omega

/-- An all-heads-zero `Step` is a ready run. -/
theorem ready_of_step {t s n : ℕ} {p : Machine t s} {A A' : Fin t → List Bool}
    (h : Step p n (fun _ => 0) A (fun _ => 0) A') : ClockJoin.ReadyRun p n A A' := by
  obtain ⟨r, hr, hH, hT, hs⟩ := h
  exact ⟨r, hr, hT, fun i => by rw [hH], hs⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Shell
