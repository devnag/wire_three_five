import Proof.Wire_3_5.UnionMachine.NumsPh3

/-! # NW phase (b), part 1: the request copied onto the decode's request stream

Phase (b) (`NumsPh3.PhB`, the THR requests' `V = |PrimeIndex(cut)|·|E|·Q`) reuses the THR decode pieces, which read
the framed request on stream `0` of the C4 cell bank. **`inW`**: measure the input `frame w` on `sIn` (`measW`), rewind
it, copy the framed word onto the blank stream `0` (`CarWM.copyFrameW`), rewind both, clear the scratch registers
(`460 … 462`). **`in_spec`**: stream `0 := frame w` (head `0`), `sIn` kept (head `0`), every other stream and every
register kept.

Paper quantity of the main type: the final pass's input word `fpIn` (the request word, then the seed word, P3:3044-3048)
on the decode's request stream. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.UnionMachine

/-- The input stage's scratch registers. -/
def rL : Fin LNR := ⟨460, by decide⟩
def rC : Fin LNR := ⟨461, by decide⟩
def rTm : Fin LNR := ⟨462, by decide⟩

variable (cap : ℕ) (x : ℕ)

/-- Measure `sIn` into `rL`, rewind it. -/
def measInW : WM (LNS x) LNR :=
  .seq (SymDec.measW (NumsPh2.sIn x) rL) (.seq (FinalPass.Hash4.wcopyR rL rC rTm) (.seq (ParseNat.dbl rC rTm)
    (WM.rewind (NumsPh2.sIn x) rC)))

/-- Rewind a stream by `2·rL + b` (`b ∈ {0, 1}` extra steps). -/
def rewW (s : Fin (LNS x + 1)) (b : Bool) : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR rL rC rTm) (.seq (ParseNat.dbl rC rTm) (.seq (if b then .inc rC else .skip)
    (WM.rewind s rC)))

/-- **The input copied** onto stream `0`. -/
def inW : WM (LNS x) LNR :=
  .seq (measInW x) (.seq (CarWM.copyFrameW (NumsPh2.sIn x) (sk x 0)) (.seq (rewW x (NumsPh2.sIn x) false)
    (.seq (rewW x (sk x 0) true) (WM.clear rL))))

theorem sIn_ne0 : NumsPh2.sIn x ≠ sk x 0 := fun e => by
  have := congrArg Fin.val e; rw [NumsPh2.sIn_val, sk_val] at this; simp at this

theorem frame_len (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [frame_eq_frameP]; unfold frameP; simp; ring

theorem measIn_spec (w : List Bool) (σ : WState (LNS x) LNR) (hin : σ.st (NumsPh2.sIn x) = frame w)
    (hih : σ.sh (NumsPh2.sIn x) = 0) (zL : σ.val rL = 0) (zC : σ.val rC = 0) (zT : σ.val rTm = 0)
    (hcap : 2 * w.length + 2 ≤ cap) :
    WExec cap (measInW x) σ (σ.setv rL w.length) (9 * w.length + 1 + 12 * UnaryPow.sq cap) := by
  have hl := UnaryPow.lin_le_sq cap
  have d1 : rC ≠ rL := by decide
  have d2 : rTm ≠ rL := by decide
  have d3 : rTm ≠ rC := by decide
  have e1 := SymDec.meas_spec cap (NumsPh2.sIn x) rL w 0 σ hin hih zL (by omega)
  have e2 := SparseNum.copy1 cap rL rC rTm (by decide) (by decide) (by decide) (0 + w.length)
    ((σ.seth (NumsPh2.sIn x) (2 * w.length)).setv rL (0 + w.length)) (by simp)
    (by simp [Function.update_apply, d1, zC]) (by simp [Function.update_apply, d2, zT]) (by omega)
  have e3 := FiltNum.dbl1 cap rC rTm (by decide) (0 + w.length)
    (((σ.seth (NumsPh2.sIn x) (2 * w.length)).setv rL (0 + w.length)).setv rC (0 + w.length)) (by simp)
    (by simp [Function.update_apply, d2, d3, zT]) (by omega)
  have e4 := wrewind_spec cap (NumsPh2.sIn x) rC (2 * (0 + w.length))
    ((((σ.seth (NumsPh2.sIn x) (2 * w.length)).setv rL (0 + w.length)).setv rC (0 + w.length)).setv rC
      (2 * (0 + w.length))) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = NumsPh2.sIn x
    · subst hi; simp [hih]
    · simp [Function.update_apply, hi]
  · rfl
  · funext r
    by_cases hr : r = rC
    · subst hr; simp [Function.update_apply, zC, d1]
    · by_cases hr' : r = rL
      · subst hr'; simp [Function.update_apply, Ne.symm d1]
      · simp [Function.update_apply, hr, hr']
  · rfl

theorem rew_spec (s : Fin (LNS x + 1)) (b : Bool) (wl : ℕ) (σ : WState (LNS x) LNR) (hL : σ.val rL = wl)
    (zC : σ.val rC = 0) (zT : σ.val rTm = 0) (hh : σ.sh s = 2 * wl + (if b then 1 else 0))
    (hcap : 2 * wl + 2 ≤ cap) :
    WExec cap (rewW x s b) σ (σ.seth s 0) (5 * (2 * wl + 1) + 1 + 12 * UnaryPow.sq cap) := by
  have hl := UnaryPow.lin_le_sq cap
  have d1 : rC ≠ rL := by decide
  have d3 : rTm ≠ rC := by decide
  have e2 := SparseNum.copy1 cap rL rC rTm (by decide) (by decide) (by decide) wl σ hL zC zT (by omega)
  have e3 := FiltNum.dbl1 cap rC rTm (by decide) wl (σ.setv rC wl) (by simp) (by simp [Function.update_apply, d3, zT])
    (by omega)
  cases b with
  | false =>
    have e4 := WExec.skip (cap := cap) ((σ.setv rC wl).setv rC (2 * wl))
    have e5 := wrewind_spec cap s rC (2 * wl) ((σ.setv rC wl).setv rC (2 * wl)) (by simp) (by simp; omega)
    refine WExec.cast cap (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = s
      · subst hi; simp at hh ⊢; omega
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = rC
      · subst hr; simp [zC]
      · simp [Function.update_apply, hr]
    · rfl
  | true =>
    have e4 := SparseNum.inc1 cap rC (2 * wl) ((σ.setv rC wl).setv rC (2 * wl)) (by simp) (by omega)
    have e5 := wrewind_spec cap s rC (2 * wl + 1) (((σ.setv rC wl).setv rC (2 * wl)).setv rC (2 * wl + 1)) (by simp)
      (by simp; omega)
    refine WExec.cast cap (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = s
      · subst hi; simp at hh ⊢; omega
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = rC
      · subst hr; simp [zC]
      · simp [Function.update_apply, hr]
    · rfl

/-- **The input copied**: stream `0 := frame w` (head `0`), `sIn` kept (head `0`), every other stream, every register
and the cell kept. -/
theorem in_spec (w : List Bool) (σ : WState (LNS x) LNR) (hin : σ.st (NumsPh2.sIn x) = frame w)
    (hih : σ.sh (NumsPh2.sIn x) = 0) (h0 : σ.st (sk x 0) = []) (h0h : σ.sh (sk x 0) = 0) (zL : σ.val rL = 0)
    (zC : σ.val rC = 0) (zT : σ.val rTm = 0) (hcap : 2 * w.length + 2 ≤ cap) :
    ∃ τ c, WExec cap (inW x) σ τ c ∧ c ≤ 40 * w.length + 60 * UnaryPow.sq cap ∧
      τ.st (sk x 0) = frame w ∧ τ.sh (sk x 0) = 0 ∧ τ.st (NumsPh2.sIn x) = frame w ∧ τ.sh (NumsPh2.sIn x) = 0 ∧
      (∀ i, i ≠ sk x 0 → i ≠ NumsPh2.sIn x → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧
      τ.cell = σ.cell := by
  have hl := UnaryPow.lin_le_sq cap
  have hne := sIn_ne0 x
  have e1 := measIn_spec cap x w σ hin hih zL zC zT hcap
  obtain ⟨σ2, e2, c2, c2h, n2, n2h, o2, v2, cl2⟩ := CarWM.copyFrame_spec cap (NumsPh2.sIn x) (sk x 0) hne [] w []
    (σ.setv rL w.length) (by simp [hin]) (by simp [hih]) (by simp [h0h, h0])
  simp only [WState.setv, h0, List.nil_append, List.length_nil, Nat.zero_add] at c2 n2 n2h
  have v2L : σ2.val rL = w.length := by rw [v2]; simp
  have v2C : σ2.val rC = 0 := by
    rw [v2]; show Function.update σ.val rL w.length rC = 0; rw [Function.update_of_ne (by decide)]; exact zC
  have v2T : σ2.val rTm = 0 := by
    rw [v2]; show Function.update σ.val rL w.length rTm = 0; rw [Function.update_of_ne (by decide)]; exact zT
  have e3 := rew_spec cap x (NumsPh2.sIn x) false w.length σ2 v2L v2C v2T (by simp [n2h]) hcap
  have e4 := rew_spec cap x (sk x 0) true w.length (σ2.seth (NumsPh2.sIn x) 0) (by simp [v2L]) (by simp [v2C])
    (by simp [v2T]) (by simp [Function.update_apply, Ne.symm hne, c2h, c2, frame_len]) hcap
  have e5 := wclear_spec cap rL w.length ((σ2.seth (NumsPh2.sIn x) 0).seth (sk x 0) 0) (by simp [v2L]) (by simp [v2L]; omega)
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c2]
  · simp
  · simp [Function.update_apply, hne, n2, hin]
  · simp [Function.update_apply, hne]
  · intro i hi0 hin'
    have o := o2 i hin' hi0
    simp [Function.update_apply, hi0, hin']
    exact ⟨o.1, by rw [o.2]; simp [Function.update_apply]⟩
  · funext r
    by_cases hr : r = rL
    · subst hr; simp [zL]
    · simp [Function.update_apply, hr, v2]
  · simp [cl2]

end NearCubicWires.WireExponent3_5.PrimT.NwB
