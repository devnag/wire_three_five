import Proof.Wire_3_5.UnionMachine.FrontFill

/-! # C6 front kit: register programs and fills as ready runs

The front docks many register programs (C5's `WM`) and fills (`FrontFill.fillP`); this kit states each as a
`ClockJoin.ReadyRun` (every head at `0` before and after), the form `ReadyRun.focus` / `ClockJoin.join` compose.

* **`wm_ready`**: a `WExec` derivation whose entry and exit states have every stream head and register at `0` is a
  ready run of the compiled program, between the encoded banks.
* **`fill_ready`**: the fill from a count `1^W` onto blank targets, as a ready run.
* **`cell_ready`**: one write of `[false]` on a blank cell tape.
* `wenc_stream`, `wenc_cell`, `wenc_reg`: the encoded bank's tapes. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- A step between zero heads is a ready run. -/
theorem ready_of_step {t s : ℕ} {p : Machine t s} {n : ℕ} {A A' : Fin t → List Bool}
    (h : Step p n (fun _ => 0) A (fun _ => 0) A') : ClockJoin.ReadyRun p n A A' := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  exact ⟨r, hr, ht, fun i => by rw [hh], hs⟩

theorem wenc_H_zero {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j; simp only [wenc]; split <;> simp [hs, hv]

/-- **A register program as a ready run.** -/
theorem wm_ready {ns nr : ℕ} (P : WM ns nr) (cap n : ℕ) (σ τ : WState ns nr) (h : WExec cap P σ τ n)
    (hs0 : ∀ i, σ.sh i = 0) (hv0 : ∀ r, σ.val r = 0) (hs1 : ∀ i, τ.sh i = 0) (hv1 : ∀ r, τ.val r = 0) :
    ClockJoin.ReadyRun P.toProg.compile n (wenc cap σ).A (wenc cap τ).A := by
  have hstep := (WExec.exec cap h).step
  rw [wenc_H_zero cap σ hs0 hv0, wenc_H_zero cap τ hs1 hv1] at hstep
  exact ready_of_step hstep

theorem wenc_cell {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) : (wenc cap σ).A cTape = [σ.cell] := by
  simp [wenc, role_cTape]

/-- **The fill as a ready run**: from the count `1^W` and blank targets and marker tape (every head at `0`), every
target and the marker tape hold `replicate (2W+3) false`; nothing else changes. -/
theorem fill_ready {t : ℕ} (cnt aux : Fin t) (tgt : Fin t → Bool) (A : Fin t → List Bool) (W : ℕ)
    (hca : cnt ≠ aux) (hct : tgt cnt = false) (hat : tgt aux = false) (hcw : A cnt = List.replicate W true)
    (hA : ∀ i, FrontFill.side aux tgt i → A i = []) :
    ClockJoin.ReadyRun (FrontFill.fillP cnt aux tgt).compile (11 * W + 20) A
      (fun i => if FrontFill.side aux tgt i then List.replicate (2 * W + 3) false else A i) := by
  have e := FrontFill.fillP_exec cnt aux tgt (fun _ => 0) A hca hct hat W hcw (fun _ _ => rfl) hA
  have hH : (FrontFill.stB cnt aux tgt (fun _ => 0) A W 0).H = fun _ => 0 := by
    funext i; simp only [FrontFill.stB]; split_ifs <;> omega
  have hA' : (FrontFill.stB cnt aux tgt (fun _ => 0) A W 0).A =
      fun i => if FrontFill.side aux tgt i then List.replicate (2 * W + 3) false else A i := by
    funext i
    by_cases hs : FrontFill.side aux tgt i
    · rw [if_pos hs]; exact FrontFill.stB_zero_A cnt aux tgt (fun _ => 0) A W i hs
    · rw [if_neg hs]
      simp only [FrontFill.stB]
      have ht : tgt i = false := by
        cases h : tgt i
        · rfl
        · exact absurd (Or.inl h) hs
      have hx : i ≠ aux := fun h => hs (Or.inr h)
      simp [ht, hx]
  have hs := Exec.step e
  rw [hH, hA'] at hs
  exact ready_of_step hs

/-- The one-write program: `[false]` on the cell tape `c`. -/
def cellP {t : ℕ} (c : Fin t) : Prog t := .act (fun i => if i = c then some false else none) (fun _ => .stay)

theorem cell_ready {t : ℕ} (c : Fin t) (A : Fin t → List Bool) (hc : A c = []) :
    ClockJoin.ReadyRun (cellP c).compile 1 A (Function.update A c [false]) := by
  have e := Exec.act (⟨fun _ => 0, A⟩ : Bank t) (fun i => if i = c then some false else none) (fun _ => .stay)
  have hs := Exec.step e
  have hA : ((⟨fun _ => 0, A⟩ : Bank t).act (fun i => if i = c then some false else none) (fun _ => .stay)).A =
      Function.update A c [false] := by
    funext i
    by_cases hi : i = c
    · subst hi; simp [Bank.act, hc, writeTapeBit]
    · simp [Bank.act, hi]
  rw [hA] at hs
  exact ready_of_step hs


end NearCubicWires.WireExponent3_5.UnionMachine.FrontKit
