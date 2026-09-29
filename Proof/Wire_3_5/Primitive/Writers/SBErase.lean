import Proof.Wire_3_5.Primitive.Writers.WriteNat

/-! # SB, part 3: erasing a scratch stream to `0^T`

The pool writers' contract (`CoreWordsM`) leaves every scratch stream as `0^ℓ`. A stream of length at most `T`
(head at `0`) is overwritten with `T` blanks and rewound (the counter `c` holds `T`, the position counter `d` starts
at `0`; both end at `0`):

* `writeTapeBit_blank`; `wipeW`, **`wipe_spec`** (`replicate h false ++ e ↦ replicate (h + v) false`);
* `eraseW`, **`erase_spec`** (`e ↦ replicate T false`, head `0`, cost `16T + 3`).

Paper quantity: none (machine plumbing for the writers' blank scratch). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBErase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ} (cap : ℕ)

theorem writeTapeBit_blank : ∀ (h : ℕ) (e : List Bool),
    writeTapeBit (List.replicate h false ++ e) h false = List.replicate (h + 1) false ++ e.tail
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | h + 1, e => by
    rw [List.replicate_succ, List.cons_append]
    show false :: writeTapeBit (List.replicate h false ++ e) h false = _
    rw [writeTapeBit_blank h e]
    rfl

/-- Blank `v` cells from the head (counter `c`), counting the moves in `d`. -/
def wipeW (i : Fin (ns + 1)) (c d : Fin nr) : WM ns nr := .whr c (.seq (.dec c) (.seq (.wr i false) (WM.fwdC i d)))

theorem wipe_spec (i : Fin (ns + 1)) (c d : Fin nr) (hcd : c ≠ d) :
    ∀ (v : ℕ) (σ : WState ns nr) (h : ℕ) (e : List Bool), σ.val c = v → σ.sh i = h →
      σ.st i = List.replicate h false ++ e → e.length ≤ v → σ.val d + v ≤ cap → v ≤ cap →
      WExec cap (wipeW i c d) σ
        (((σ.sets i (List.replicate (h + v) false)).seth i (h + v)).setv c 0 |>.setv d (σ.val d + v)) (11 * v + 1) := by
  intro v
  induction v with
  | zero =>
    intro σ h e hv hh he hl _ _
    have e0 : e = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst e0
    have eq : (((σ.sets i (List.replicate (h + 0) false)).seth i (h + 0)).setv c 0).setv d (σ.val d + 0) = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = i
        · subst hj; simp [hh]
        · simp [Function.update_of_ne hj]
      · funext j; by_cases hj : j = i
        · subst hj; simp [he]
        · simp [Function.update_of_ne hj]
      · funext j; by_cases hj : j = d
        · subst hj; simp
        · by_cases hj2 : j = c
          · subst hj2; simp [Function.update_of_ne hj, hv]
          · simp [Function.update_of_ne hj, Function.update_of_ne hj2]
      · rfl
    rw [eq]
    exact WExec.whrF hv
  | succ v ih =>
    intro σ h e hv hh he hl hd hc
    have h1 := WExec.dec (cap := cap) c σ (by omega)
    set σ1 := σ.setv c (σ.val c - 1) with hσ1
    have h2 := WExec.wr (cap := cap) i false σ1
    set σ2 := σ1.sets i (writeTapeBit (σ1.st i) (σ1.sh i) false) with hσ2
    have hw : writeTapeBit (σ1.st i) (σ1.sh i) false = List.replicate (h + 1) false ++ e.tail := by
      simp only [hσ1, WState.setv_st, WState.setv_sh, he, hh]; exact writeTapeBit_blank h e
    have h3 := wfwdC_spec cap i d σ2 (by simp [hσ2, hσ1, Function.update_of_ne (Ne.symm hcd)]; omega)
    set σ3 := (σ2.seth i (σ2.sh i + 1)).setv d (σ2.val d + 1) with hσ3
    have hv3 : σ3.val c = v := by simp [hσ3, hσ2, hσ1, Function.update_of_ne hcd]; omega
    have hh3 : σ3.sh i = h + 1 := by simp [hσ3, hσ2, hσ1, hh]
    have he3 : σ3.st i = List.replicate (h + 1) false ++ e.tail := by simp [hσ3, hσ2, hw]
    have hl3 : e.tail.length ≤ v := by simp; omega
    have hd3 : σ3.val d + v ≤ cap := by simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hcd)]; omega
    have h4 := ih σ3 (h + 1) e.tail hv3 hh3 he3 hl3 hd3 (by omega)
    have hb := WExec.whrT (show σ.val c ≠ 0 by omega) (WExec.seq h1 (WExec.seq h2 h3)) h4
    refine WExec.cast cap hb ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = i
      · subst hj; simp [hσ3, hσ2, hσ1]; omega
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne hj]
    · funext j; by_cases hj : j = i
      · subst hj; simp [hσ3, hσ2, hσ1]; ring_nf
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne hj]
    · funext j; by_cases hj : j = d
      · subst hj; simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hcd)]; omega
      · by_cases hj2 : j = c
        · subst hj2; simp [hσ3, hσ2, hσ1, Function.update_of_ne hj]
        · simp [hσ3, hσ2, hσ1, Function.update_of_ne hj, Function.update_of_ne hj2]
    · rfl

/-- **Erase a scratch stream**: blank `T` cells from `0`, then rewind. -/
def eraseW (i : Fin (ns + 1)) (c d : Fin nr) : WM ns nr := .seq (wipeW i c d) (WM.rewind i d)

theorem erase_spec (i : Fin (ns + 1)) (c d : Fin nr) (hcd : c ≠ d) (T : ℕ) (σ : WState ns nr)
    (hv : σ.val c = T) (hd0 : σ.val d = 0) (hh : σ.sh i = 0) (hl : (σ.st i).length ≤ T) (hc : T ≤ cap) :
    WExec cap (eraseW i c d) σ ((σ.sets i (List.replicate T false)).setv c 0) (16 * T + 3) := by
  have h1 := wipe_spec cap i c d hcd T σ 0 (σ.st i) hv hh (by simp) hl (by omega) hc
  set τ := (((σ.sets i (List.replicate (0 + T) false)).seth i (0 + T)).setv c 0).setv d (σ.val d + T) with hτ
  have h2 := wrewind_spec cap i d T τ (by simp [hτ, hd0]) (by simp [hτ, hd0]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [hτ, hh]
    · simp [hτ, Function.update_of_ne hj]
  · funext j; by_cases hj : j = i
    · subst hj; simp [hτ]
    · simp [hτ, Function.update_of_ne hj]
  · funext j; by_cases hj : j = d
    · subst hj; simp [hτ, Function.update_of_ne (Ne.symm hcd), hd0]
    · simp [hτ, Function.update_of_ne hj]
  · rfl

end NearCubicWires.WireExponent3_5.PrimAsm.SBErase
