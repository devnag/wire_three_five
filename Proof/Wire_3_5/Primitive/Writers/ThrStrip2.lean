import Proof.Wire_3_5.Primitive.Writers.ThrStrip1

/-! # c4 THR block, the request's strip, part 2: rewinding, counting down, copying the pairs

* `rew2W` (rewind two cells per count), `suf1W` (count the remaining pairs down), `cpyW` (copy `k` pairs from stream
  `i` to the end of stream `o`), with their runs.

Paper quantity of the main type: none (the loops' runs on the marked stream). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Rewinding two cells per count -/

def rew2W (i : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .whr r (.seq (.dec r) (.seq (.bwd i) (.bwd i)))

theorem rew2W_spec (i : Fin (ns + 1)) (r : Fin nr) (m : ℕ) (σ : WState ns nr) (hi : σ.sh i = 2 * m)
    (hr : σ.val r = m) (hm : m ≤ cap) :
    WExec cap (rew2W i r) σ ((σ.seth i 0).setv r 0) (7 * m + 1) := by
  set S : ℕ → WState ns nr := fun q => (σ.seth i (2 * m - 2 * q)).setv r (m - q) with hSd
  have l := UnaryPow.flagLoop cap r (.seq (.dec r) (.seq (.bwd i) (.bwd i))) 5 m S
    (fun k hk => by simp [hSd]; omega) (by simp [hSd])
    (fun k hk => by
      have h1 := WExec.dec (cap := cap) r (S k) (by simp [hSd]; omega)
      have h2 := WExec.bwd (cap := cap) i ((S k).setv r ((S k).val r - 1))
      have h3 := WExec.bwd (cap := cap) i (((S k).setv r ((S k).val r - 1)).seth i
        (((S k).setv r ((S k).val r - 1)).sh i - 1))
      refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
      apply WState.eq
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hSd, Function.update_apply]; omega
        · simp [hSd, Function.update_apply, hj]
      · funext j; simp [hSd]
      · funext j
        by_cases hj : j = r
        · subst hj; simp [hSd, Function.update_apply]; omega
        · simp [hSd, Function.update_apply, hj]
      · simp [hSd])
  have e0 : S 0 = σ := by
    apply WState.eq
    · funext j
      by_cases hj : j = i
      · subst hj; simp [hSd, Function.update_apply, hi]
      · simp [hSd, Function.update_apply, hj]
    · funext j; simp [hSd]
    · funext j
      by_cases hj : j = r
      · subst hj; simp [hSd, Function.update_apply, hr]
      · simp [hSd, Function.update_apply, hj]
    · simp [hSd]
  have em : S m = (σ.seth i 0).setv r 0 := by simp [hSd]
  rw [e0, em] at l
  exact WExec.mono l (by omega)

/-! ## Counting the remaining pairs down -/

def suf1W (i : Fin (ns + 1)) (a : Fin nr) : WM ns nr := .whs i (.seq (.fwd i) (.seq (.fwd i) (.dec a)))

theorem suf1W_spec (i : Fin (ns + 1)) (a : Fin nr) (u : List Bool) :
    ∀ (σ : WState ns nr) (pre : List Bool), σ.st i = pre ++ marks u ++ [false] → σ.sh i = pre.length →
      σ.val a ≤ cap →
      WExec cap (suf1W i a) σ ((σ.seth i (pre.length + 2 * u.length)).setv a (σ.val a - u.length))
        (7 * u.length + 1) := by
  induction u with
  | nil =>
    intro σ pre hst hsh ha
    have hbit : wbit σ i = false := by
      simp only [wbit, hst, hsh]; simp [marks, readTapeBit]
    have e : (σ.seth i (pre.length + 2 * ([] : List Bool).length)).setv a (σ.val a - ([] : List Bool).length) = σ := by
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs with h
        · subst h; simp [hsh]
        · rfl
      · simp
      · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs with h
        · subst h; simp
        · rfl
      · simp
    rw [e]
    exact WExec.mono (WExec.whsF hbit) (by omega)
  | cons x u ih =>
    intro σ pre hst hsh ha
    have hbit : wbit σ i = true := by
      simp only [wbit, hst, hsh, marks_cons]
      have := rd_at pre (x :: (marks u ++ [false])) true
      simpa [List.append_assoc] using this
    have e1 := WExec.fwd (cap := cap) i σ
    have e2 := WExec.fwd (cap := cap) i (σ.seth i (σ.sh i + 1))
    have e3 := WExec.dec (cap := cap) a ((σ.seth i (σ.sh i + 1)).seth i ((σ.seth i (σ.sh i + 1)).sh i + 1))
      (by simp; exact ha)
    set σ1 := (σ.seth i (pre ++ [true, x]).length).setv a (σ.val a - 1) with hσ1
    have hs1 : ((σ.seth i (σ.sh i + 1)).seth i ((σ.seth i (σ.sh i + 1)).sh i + 1)).setv a
        (((σ.seth i (σ.sh i + 1)).seth i ((σ.seth i (σ.sh i + 1)).sh i + 1)).val a - 1) = σ1 := by
      rw [hσ1]
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
      · simp
      · simp
      · simp
    rw [hs1] at e3
    have st1 : σ1.st i = (pre ++ [true, x]) ++ marks u ++ [false] := by
      rw [hσ1]; simp [hst, marks_cons]
    have sh1 : σ1.sh i = (pre ++ [true, x]).length := by rw [hσ1]; simp
    have va : σ1.val a ≤ cap := by rw [hσ1]; simp; omega
    have h2 := ih σ1 (pre ++ [true, x]) st1 sh1 va
    have ef : (σ1.seth i ((pre ++ [true, x]).length + 2 * u.length)).setv a (σ1.val a - u.length) =
        (σ.seth i (pre.length + 2 * (x :: u).length)).setv a (σ.val a - (x :: u).length) := by
      rw [hσ1]
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs <;> simp_all <;> omega
      · simp
      · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs <;> simp_all <;> omega
      · simp
    rw [ef] at h2
    exact WExec.mono (WExec.whsT hbit (WExec.seq e1 (WExec.seq e2 e3)) h2) (by simp; omega)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
