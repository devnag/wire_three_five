import Proof.Wire_3_5.UnionMachine.FrontCapW

/-! # C6 front, the install (P3:3669-3691; `Plan.bankA`): the loop's kept tapes from the front's results

The loop's bank at its entry (`Plan.bankA cap R Lg kept`) holds: the call table `tbl` (head `0`), the cell `[false]`, the
rounding register and the six accumulators as registers of capacity `cap` (heads at their values), `0^R` on every
scratch tape, the log `0^{R+1}`, the driver `1^R`. A word program writes the kept tapes, the driver and the log as
STREAMS docked onto the loop's tapes (the scratch is blanked afterwards by base's selected erase):
* `onesW` (the driver `1^R` from the ruler `U R`, head back to `0`), `zerosW` (the log `0^{R+1}`), `cellW`;
* `regTW` (`regTape cap v` from the ruler `U cap` and `v` in a register, head at `v`);
* `tblW` (the table word, copied under a register count, head back to `0`).

Paper quantity of the main type: the loop's bank at its entry (the table, the accumulators' start, `p`, the capacities). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontInstall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCapW

section Kit
variable {ns nr : ℕ} (cap : ℕ)

theorem wrOnes_rep : ∀ (k j : ℕ), wrOnes (List.replicate j true) j k = List.replicate (j + k) true
  | 0, j => by simp [wrOnes]
  | k + 1, j => by
    simp only [wrOnes]
    rw [show writeTapeBit (List.replicate j true) j true = List.replicate (j + 1) true by
      rw [write_rep_true j j le_rfl]; congr 1; omega, wrOnes_rep k (j + 1)]
    congr 1; omega

/-- Write `k` zeros from position `h`. -/
def wrZeros : List Bool → ℕ → ℕ → List Bool
  | l, _, 0 => l
  | l, h, k + 1 => wrZeros (writeTapeBit l h false) (h + 1) k

theorem write_rep_false_end (j : ℕ) : writeTapeBit (List.replicate j false) j false = List.replicate (j + 1) false := by
  induction j with
  | zero => simp [writeTapeBit]
  | succ j ih => rw [List.replicate_succ]; simp only [writeTapeBit]; rw [ih]; simp [List.replicate_succ]

theorem wrZeros_rep : ∀ (k j : ℕ), wrZeros (List.replicate j false) j k = List.replicate (j + k) false
  | 0, j => by simp [wrZeros]
  | k + 1, j => by
    simp only [wrZeros]
    rw [write_rep_false_end j, wrZeros_rep k (j + 1)]
    congr 1; omega

/-- The zero loop: while `a` reads `1`, write `0` on `b` and advance both. -/
def zeroLoop (a b : Fin (ns + 1)) : WM ns nr := .whs a (.seq (.wr b false) (.seq (.fwd b) (.fwd a)))

def zState (a b : Fin (ns + 1)) (σ : WState ns nr) (k : ℕ) : WState ns nr :=
  ((σ.sets b (wrZeros (σ.st b) (σ.sh b) k)).seth b (σ.sh b + k)).seth a (σ.sh a + k)

theorem zeroLoop_spec (a b : Fin (ns + 1)) (hab : a ≠ b) : ∀ (k : ℕ) (σ : WState ns nr),
    (∀ j < k, readTapeBit (σ.st a) (σ.sh a + j) = true) → readTapeBit (σ.st a) (σ.sh a + k) = false →
    WExec cap (zeroLoop a b) σ (zState a b σ k) (7 * k + 1)
  | 0, σ, _, hstop => by
    have h := WExec.whsF (cap := cap) (P := .seq (.wr b false) (.seq (.fwd b) (.fwd a))) (i := a) (σ := σ)
      (by simpa [wbit] using hstop)
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hia : i = a
      · subst hia; simp [zState, Function.update_apply]
      · by_cases hib : i = b
        · subst hib; simp [zState, Function.update_apply, hia]
        · simp [zState, Function.update_apply, hia, hib]
    · intro i
      by_cases hib : i = b
      · subst hib; simp [zState, wrZeros, Function.update_apply]
      · simp [zState, Function.update_apply, hib]
    · rfl
    · rfl
  | k + 1, σ, hrun, hstop => by
    have hba : b ≠ a := fun h => hab h.symm
    have h0 := hrun 0 (by omega)
    set σ1 : WState ns nr := ((σ.sets b (writeTapeBit (σ.st b) (σ.sh b) false)).seth b (σ.sh b + 1)).seth a
      (σ.sh a + 1) with hσ1
    have hbody : WExec cap (.seq (.wr b false) (.seq (.fwd b) (.fwd a))) σ σ1 5 := by
      have e1 := WExec.wr (cap := cap) b false σ
      have e2 := WExec.fwd (cap := cap) b (σ.sets b (writeTapeBit (σ.st b) (σ.sh b) false))
      have e3 := WExec.fwd (cap := cap) a ((σ.sets b (writeTapeBit (σ.st b) (σ.sh b) false)).seth b
        ((σ.sets b (writeTapeBit (σ.st b) (σ.sh b) false)).sh b + 1))
      refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
      simp only [σ1, WState.seth_sh, WState.sets_sh, Function.update_of_ne hab]
    have s1a : σ1.st a = σ.st a := by simp [σ1, Function.update_of_ne hab]
    have h1a : σ1.sh a = σ.sh a + 1 := by simp [σ1]
    have ih := zeroLoop_spec a b hab k σ1 (fun j hj => by
        rw [s1a, h1a, show σ.sh a + 1 + j = σ.sh a + (j + 1) by omega]; exact hrun (j + 1) (by omega))
      (by rw [s1a, h1a, show σ.sh a + 1 + k = σ.sh a + (k + 1) by omega]; exact hstop)
    have h := WExec.whsT (cap := cap) (i := a) (by simpa [wbit] using h0) hbody ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hia : i = a
      · subst hia; simp [zState, σ1, Function.update_apply, hab]; omega
      · by_cases hib : i = b
        · subst hib; simp [zState, σ1, Function.update_apply, hia]; omega
        · simp [zState, σ1, Function.update_apply, hia, hib]
    · intro i
      by_cases hib : i = b
      · subst hib; simp [zState, σ1, Function.update_apply, wrZeros, hab, hba]
      · simp [zState, σ1, Function.update_apply, hib]
    · rfl
    · rfl

/-- The counting rewind: `a` back over its ones to the sentinel, `b` back by as many cells. -/
def bwd2Loop (a b : Fin (ns + 1)) : WM ns nr := .whs a (.seq (.bwd b) (.bwd a))

theorem bwd2Loop_spec (a b : Fin (ns + 1)) (hab : a ≠ b) : ∀ (k : ℕ) (σ : WState ns nr), σ.sh a = k → k ≤ σ.sh b →
    (∀ j, 1 ≤ j → j ≤ k → readTapeBit (σ.st a) j = true) → readTapeBit (σ.st a) 0 = false →
    WExec cap (bwd2Loop a b) σ ((σ.seth a 0).seth b (σ.sh b - k)) (5 * k + 1)
  | 0, σ, hk, _, _, h0 => by
    have h := WExec.whsF (cap := cap) (P := .seq (.bwd b) (.bwd a)) (i := a) (σ := σ) (by simpa [wbit, hk] using h0)
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hia : i = a
      · subst hia; simp [Function.update_apply, hk, hab]
      · by_cases hib : i = b
        · subst hib; simp [Function.update_apply]
        · simp [Function.update_apply, hia, hib]
    · intro i; rfl
    · rfl
    · rfl
  | k + 1, σ, hk, hkb, hrun, h0 => by
    have hba : b ≠ a := fun h => hab h.symm
    have e1 := WExec.bwd (cap := cap) b σ
    have e2 := WExec.bwd (cap := cap) a (σ.seth b (σ.sh b - 1))
    set σ1 := (σ.seth b (σ.sh b - 1)).seth a ((σ.seth b (σ.sh b - 1)).sh a - 1) with hσ1
    have h1a : σ1.sh a = k := by simp [σ1, Function.update_of_ne hab, hk]
    have h1b : σ1.sh b = σ.sh b - 1 := by simp [σ1, Function.update_of_ne hba]
    have ih := bwd2Loop_spec a b hab k σ1 h1a (by rw [h1b]; omega) (fun j h1 h2 => by
      simpa [σ1] using hrun j h1 (by omega)) (by simpa [σ1] using h0)
    have h := WExec.whsT (cap := cap) (i := a) (P := .seq (.bwd b) (.bwd a))
      (by simpa [wbit, hk] using hrun (k + 1) (by omega) le_rfl) (WExec.seq e1 e2) ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hia : i = a
      · subst hia; simp [σ1, Function.update_apply, hab]
      · by_cases hib : i = b
        · subst hib; simp [σ1, Function.update_apply, hia]; omega
        · simp [σ1, Function.update_apply, hia, hib]
    · intro i; rfl
    · rfl
    · rfl

end Kit

/-! ## The driver, the log, the cell -/

section Tapes
variable {ns nr : ℕ} (cap : ℕ)

/-- **The driver** `1^R` from the ruler `U R`, its head back to `0`. -/
def onesW (sR d : Fin (ns + 1)) : WM ns nr := .seq (cpLoop sR d) (.seq (.bwd sR) (.seq (bwd2Loop sR d) (.fwd sR)))

theorem onesW_spec (sR d : Fin (ns + 1)) (hne : sR ≠ d) (σ : WState ns nr) (R : ℕ) (hR : σ.st sR = U R)
    (hRh : σ.sh sR = 1) (hd : σ.st d = []) (hdh : σ.sh d = 0) :
    WExec cap (onesW sR d) σ ((σ.sets d (List.replicate R true)).seth d 0) (12 * R + 7) := by
  have hdn : d ≠ sR := fun h => hne h.symm
  have e1 := cpLoop_spec cap sR d hne R σ (fun j hj => by rw [hR, hRh]; exact read_U_pos R _ (by omega) (by omega))
    (by rw [hR, hRh]; exact read_U_end R _ (by omega))
  set σ1 := cpState sR d σ R with hσ1
  have st1 : σ1.st sR = U R := by simp [σ1, cpState, Function.update_of_ne hne, hR]
  have sh1 : σ1.sh sR = R + 1 := by simp [σ1, cpState, hRh]; omega
  have sd1 : σ1.st d = List.replicate R true := by
    simp [σ1, cpState, hd, hdh]
    have := wrOnes_rep R 0
    simpa using this
  have shd1 : σ1.sh d = R := by simp [σ1, cpState, Function.update_of_ne hdn, hdh]
  have e2 := WExec.bwd (cap := cap) sR σ1
  set σ2 := σ1.seth sR (σ1.sh sR - 1) with hσ2
  have h2d : σ2.sh d = R := by
    simp only [σ2, WState.seth_sh]; rw [Function.update_of_ne hdn]; exact shd1
  have e3 := bwd2Loop_spec cap sR d hne R σ2 (by simp [σ2, sh1]) (by omega)
    (fun j h1 h2 => by simp only [σ2, WState.seth_st, st1]; exact read_U_pos R j h1 h2)
    (by simp only [σ2, WState.seth_st, st1]; exact read_U_zero R)
  set σ3 := (σ2.seth sR 0).seth d (σ2.sh d - R) with hσ3
  have e4 := WExec.fwd (cap := cap) sR σ3
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  apply wst_eq
  · intro i
    by_cases hi : i = sR
    · subst hi; simp [σ3, σ2, Function.update_apply, hne, hRh]
    · by_cases hid : i = d
      · subst hid; simp [σ3, σ2, σ1, cpState, Function.update_apply, hi, hdh]
      · simp [σ3, σ2, σ1, cpState, Function.update_apply, hi, hid]
  · intro i
    by_cases hid : i = d
    · subst hid; simp [σ3, σ2, sd1]
    · simp [σ3, σ2, σ1, cpState, Function.update_apply, hid]
  · rfl
  · rfl

/-- **The log** `0^{R+1}` from the ruler `U R`, its head back to `0`. -/
def zerosW (sR g : Fin (ns + 1)) : WM ns nr :=
  .seq (zeroLoop sR g) (.seq (.wr g false) (.seq (.bwd sR) (.seq (bwd2Loop sR g) (.fwd sR))))

theorem zerosW_spec (sR g : Fin (ns + 1)) (hne : sR ≠ g) (σ : WState ns nr) (R : ℕ) (hR : σ.st sR = U R)
    (hRh : σ.sh sR = 1) (hg : σ.st g = []) (hgh : σ.sh g = 0) :
    WExec cap (zerosW sR g) σ ((σ.sets g (List.replicate (R + 1) false)).seth g 0) (12 * R + 9) := by
  have hgn : g ≠ sR := fun h => hne h.symm
  have e1 := zeroLoop_spec cap sR g hne R σ (fun j hj => by rw [hR, hRh]; exact read_U_pos R _ (by omega) (by omega))
    (by rw [hR, hRh]; exact read_U_end R _ (by omega))
  set σ1 := zState sR g σ R with hσ1
  have st1 : σ1.st sR = U R := by simp [σ1, zState, Function.update_of_ne hne, hR]
  have sh1 : σ1.sh sR = R + 1 := by simp [σ1, zState, hRh]; omega
  have sg1 : σ1.st g = List.replicate R false := by
    simp [σ1, zState, hg, hgh]
    have := wrZeros_rep R 0
    simpa using this
  have shg1 : σ1.sh g = R := by simp [σ1, zState, Function.update_of_ne hgn, hgh]
  have e2 := WExec.wr (cap := cap) g false σ1
  set σ2 := σ1.sets g (writeTapeBit (σ1.st g) (σ1.sh g) false) with hσ2
  have sg2 : σ2.st g = List.replicate (R + 1) false := by
    simp only [σ2, WState.sets_st, Function.update_self, sg1, shg1]; exact write_rep_false_end R
  have e3 := WExec.bwd (cap := cap) sR σ2
  set σ3 := σ2.seth sR (σ2.sh sR - 1) with hσ3
  have h3g : σ3.sh g = R := by
    simp only [σ3, σ2, WState.seth_sh, WState.sets_sh]; rw [Function.update_of_ne hgn]; exact shg1
  have e4 := bwd2Loop_spec cap sR g hne R σ3 (by simp [σ3, σ2, sh1]) (by omega)
    (fun j h1 h2 => by
      simp only [σ3, σ2, WState.seth_st, WState.sets_st, Function.update_of_ne hne, st1]; exact read_U_pos R j h1 h2)
    (by simp only [σ3, σ2, WState.seth_st, WState.sets_st, Function.update_of_ne hne, st1]; exact read_U_zero R)
  set σ4 := (σ3.seth sR 0).seth g (σ3.sh g - R) with hσ4
  have e5 := WExec.fwd (cap := cap) sR σ4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
  apply wst_eq
  · intro i
    by_cases hi : i = sR
    · subst hi; simp [σ4, σ3, σ2, Function.update_apply, hne, hRh]
    · by_cases hig : i = g
      · subst hig; simp [σ4, σ3, σ2, σ1, zState, Function.update_apply, hi, hgh]
      · simp [σ4, σ3, σ2, σ1, zState, Function.update_apply, hi, hig]
  · intro i
    by_cases hig : i = g
    · subst hig; simp only [σ4, σ3, WState.seth_st]; rw [sg2]; simp
    · simp [σ4, σ3, σ2, σ1, zState, Function.update_apply, hig]
  · rfl
  · rfl

/-- **The cell** `[false]`. -/
theorem cellW_spec (c : Fin (ns + 1)) (σ : WState ns nr) (hc : σ.st c = []) (hch : σ.sh c = 0) :
    WExec cap (.wr c false) σ (σ.sets c [false]) 1 := by
  have e := WExec.wr (cap := cap) c false σ
  refine WExec.cast cap e ?_ le_rfl
  rw [hc, hch]; rfl

end Tapes

/-! ## Registers of capacity `cap`, the table -/

section Regs
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
variable {ns nr : ℕ} (cap : ℕ)

theorem wtb_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [writeTapeBit] using ih

/-- The bits `[j < r]` for `j < k`. -/
def bitsOf : ℕ → ℕ → List Bool
  | _, 0 => []
  | r, k + 1 => decide (0 < r) :: bitsOf (r - 1) k

theorem bitsOf_eq : ∀ (r k : ℕ), r ≤ k → bitsOf r k = List.replicate r true ++ List.replicate (k - r) false
  | 0, 0, _ => rfl
  | 0, k + 1, _ => by
    simp only [bitsOf, lt_irrefl, decide_false]
    rw [bitsOf_eq 0 k (by omega)]; simp [List.replicate_succ]
  | r + 1, k + 1, h => by
    simp only [bitsOf, Nat.succ_pos, decide_true, Nat.add_sub_cancel]
    rw [bitsOf_eq r k (by omega)]
    simp [List.replicate_succ]
  | r + 1, 0, h => by omega

/-- The register loop: along the ruler, write `1` while the counter is positive (decrementing it), else `0`. -/
def regLoop (dst sC : Fin (ns + 1)) (rt : Fin nr) : WM ns nr :=
  .whs sC (.seq (.ifr rt (.seq (.wr dst true) (.dec rt)) (.wr dst false)) (.seq (.fwd dst) (.fwd sC)))

theorem regLoop_spec (dst sC : Fin (ns + 1)) (hne : dst ≠ sC) (rt : Fin nr) : ∀ (k : ℕ) (σ : WState ns nr) (r : ℕ),
    σ.val rt = r → r ≤ cap → (∀ j < k, readTapeBit (σ.st sC) (σ.sh sC + j) = true) →
    readTapeBit (σ.st sC) (σ.sh sC + k) = false → σ.sh dst = (σ.st dst).length →
    WExec cap (regLoop dst sC rt) σ
      ((((σ.sets dst (σ.st dst ++ bitsOf r k)).seth dst (σ.sh dst + k)).seth sC (σ.sh sC + k)).setv rt (r - min k r))
      (10 * k + 1)
  | 0, σ, r, hr, _, _, hstop, _ => by
    have h := WExec.whsF (cap := cap) (P := .seq (.ifr rt (.seq (.wr dst true) (.dec rt)) (.wr dst false))
      (.seq (.fwd dst) (.fwd sC))) (i := sC) (σ := σ) (by simpa [wbit] using hstop)
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hi : i = sC
      · subst hi; simp [Function.update_apply]
      · by_cases hid : i = dst
        · subst hid; simp [Function.update_apply, hi]
        · simp [Function.update_apply, hi, hid]
    · intro i
      by_cases hid : i = dst
      · subst hid; simp [bitsOf]
      · simp [Function.update_apply, hid]
    · funext x; by_cases hx : x = rt
      · subst hx; simp [hr]
      · simp [Function.update_apply, hx]
    · rfl
  | k + 1, σ, r, hr, hrc, hrun, hstop, hlen => by
    have hsd : sC ≠ dst := fun h => hne h.symm
    have h0 := hrun 0 (by omega)
    set b := decide (0 < r) with hb
    set σ1 : WState ns nr := (σ.sets dst (σ.st dst ++ [b])).setv rt (r - 1) with hσ1
    have hbr : WExec cap (.ifr rt (.seq (.wr dst true) (.dec rt)) (.wr dst false)) σ σ1 4 := by
      by_cases h0r : r = 0
      · have e := WExec.wr (cap := cap) dst false σ
        have hf := WExec.ifrF (cap := cap) (r := rt) (P := .seq (.wr dst true) (.dec rt)) (by omega) e
        refine WExec.cast cap hf ?_ (by omega)
        apply wst_eq
        · intro i; rfl
        · intro i; by_cases hi : i = dst
          · subst hi; simp [σ1, hlen, wtb_end, hb, h0r]
          · simp [σ1, Function.update_apply, hi]
        · funext x; by_cases hx : x = rt
          · subst hx; simp [σ1, hr, h0r]
          · simp [σ1, Function.update_apply, hx]
        · rfl
      · have e1 := WExec.wr (cap := cap) dst true σ
        have e2 := WExec.dec (cap := cap) rt (σ.sets dst (writeTapeBit (σ.st dst) (σ.sh dst) true)) (by simp; omega)
        have ht := WExec.ifrT (cap := cap) (r := rt) (Q := .wr dst false) (by omega) (WExec.seq e1 e2)
        refine WExec.cast cap ht ?_ (by omega)
        apply wst_eq
        · intro i; rfl
        · intro i; by_cases hi : i = dst
          · subst hi; simp [σ1, hlen, wtb_end, hb]; omega
          · simp [σ1, Function.update_apply, hi]
        · funext x; by_cases hx : x = rt
          · subst hx; simp [σ1, hr]
          · simp [σ1, Function.update_apply, hx]
        · rfl
    have e3 := WExec.fwd (cap := cap) dst σ1
    have e4 := WExec.fwd (cap := cap) sC (σ1.seth dst (σ1.sh dst + 1))
    set σ2 := (σ1.seth dst (σ1.sh dst + 1)).seth sC ((σ1.seth dst (σ1.sh dst + 1)).sh sC + 1) with hσ2
    have hbody : WExec cap (.seq (.ifr rt (.seq (.wr dst true) (.dec rt)) (.wr dst false)) (.seq (.fwd dst) (.fwd sC)))
        σ σ2 8 := WExec.cast cap (WExec.seq hbr (WExec.seq e3 e4)) rfl (by omega)
    have s2C : σ2.st sC = σ.st sC := by simp [σ2, σ1, Function.update_of_ne hsd]
    have h2C : σ2.sh sC = σ.sh sC + 1 := by simp [σ2, σ1, Function.update_of_ne hsd]
    have ih := regLoop_spec dst sC hne rt k σ2 (r - 1) (by simp [σ2, σ1]) (by omega)
      (fun j hj => by rw [s2C, h2C, show σ.sh sC + 1 + j = σ.sh sC + (j + 1) by omega]; exact hrun (j + 1) (by omega))
      (by rw [s2C, h2C, show σ.sh sC + 1 + k = σ.sh sC + (k + 1) by omega]; exact hstop)
      (by simp [σ2, σ1, Function.update_of_ne hne, hlen])
    have h := WExec.whsT (cap := cap) (i := sC) (by simpa [wbit] using h0) hbody ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hi : i = sC
      · subst hi; simp [σ2, σ1, Function.update_apply, hne, hsd]; omega
      · by_cases hid : i = dst
        · subst hid; simp [σ2, σ1, Function.update_apply, hi]; omega
        · simp [σ2, σ1, Function.update_apply, hi, hid]
    · intro i
      by_cases hid : i = dst
      · subst hid; simp [σ2, σ1, bitsOf, hb]
      · simp [σ2, σ1, Function.update_apply, hid]
    · funext x; by_cases hx : x = rt
      · subst hx; simp [σ2, σ1]; omega
      · simp [σ2, σ1, Function.update_apply, hx]
    · rfl

/-- The forward count: `v` steps of `dst`, counting `rt` down. -/
def fwdR (dst : Fin (ns + 1)) (rt : Fin nr) : WM ns nr := .whr rt (.seq (.dec rt) (.fwd dst))

theorem fwdR_spec (dst : Fin (ns + 1)) (rt : Fin nr) : ∀ (v : ℕ) (σ : WState ns nr), σ.val rt = v → v ≤ cap →
    WExec cap (fwdR dst rt) σ ((σ.setv rt 0).seth dst (σ.sh dst + v)) (5 * v + 1)
  | 0, σ, hv, _ => by
    have h := WExec.whrF (cap := cap) (P := .seq (.dec rt) (.fwd dst)) (r := rt) (σ := σ) hv
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = dst
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · funext x; by_cases hx : x = rt
      · subst hx; simp [hv]
      · simp [Function.update_apply, hx]
    · rfl
  | v + 1, σ, hv, hvc => by
    have e1 := WExec.dec (cap := cap) rt σ (by omega)
    have e2 := WExec.fwd (cap := cap) dst (σ.setv rt (σ.val rt - 1))
    have ih := fwdR_spec dst rt v ((σ.setv rt (σ.val rt - 1)).seth dst ((σ.setv rt (σ.val rt - 1)).sh dst + 1))
      (by simp [hv]) (by omega)
    have h := WExec.whrT (cap := cap) (r := rt) (by omega) (WExec.seq e1 e2) ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = dst
      · subst hi; simp; omega
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · funext x; by_cases hx : x = rt
      · subst hx; simp
      · simp [Function.update_apply, hx]
    · rfl

/-- **A register of capacity `c`** written on a fresh tape from the ruler `U c` and `v` in `rv`: `regTape c v`,
head at `v`. -/
def regTW (dst sC : Fin (ns + 1)) (rv rt t2 : Fin nr) : WM ns nr :=
  .seq (initU dst) (.seq (FinalPass.Hash4.wcopyR rv rt t2) (.seq (regLoop dst sC rt) (.seq (.bwd sC)
  (.seq (bwd2Loop sC dst) (.seq (.fwd sC) (.seq (.bwd dst) (.seq (FinalPass.Hash4.wcopyR rv rt t2) (fwdR dst rt))))))))

theorem regTW_spec (dst sC : Fin (ns + 1)) (hne : dst ≠ sC) (rv rt t2 : Fin nr) (h1 : rv ≠ rt) (h2 : rv ≠ t2)
    (h3 : rt ≠ t2) (σ : WState ns nr) (c v : ℕ) (hC : σ.st sC = U c) (hCh : σ.sh sC = 1) (hd : σ.st dst = [])
    (hdh : σ.sh dst = 0) (hv : σ.val rv = v) (ht : σ.val rt = 0) (ht2 : σ.val t2 = 0) (hvc : v ≤ c) (hcap : v ≤ cap) :
    WExec cap (regTW dst sC rv rt t2) σ ((σ.sets dst (regTape c v)).seth dst v)
      (20 * c + 5 * v + 2 * UnaryPow.sq cap + 30) := by
  have hsd : sC ≠ dst := fun h => hne h.symm
  have e1 := initU_spec cap dst σ hd hdh
  set σ1 := (σ.sets dst (U 0)).seth dst 1 with hσ1
  have e2 := copy1 cap rv rt t2 h1 h2 h3 v σ1 (by simp [σ1, hv]) (by simp [σ1, ht]) (by simp [σ1, ht2]) (by omega)
  set σ2 := σ1.setv rt v with hσ2
  have c2 : σ2.st sC = U c := by simp [σ2, σ1, Function.update_of_ne hsd, hC]
  have ch2 : σ2.sh sC = 1 := by simp [σ2, σ1, Function.update_of_ne hsd, hCh]
  have e3 := regLoop_spec cap dst sC hne rt c σ2 v (by simp [σ2]) (by omega)
    (fun j hj => by rw [c2, ch2]; exact read_U_pos c _ (by omega) (by omega))
    (by rw [c2, ch2]; exact read_U_end c _ (by omega)) (by simp [σ2, σ1, U])
  set σ3 := (((σ2.sets dst (σ2.st dst ++ bitsOf v c)).seth dst (σ2.sh dst + c)).seth sC (σ2.sh sC + c)).setv rt
    (v - min c v) with hσ3
  have c3 : σ3.st sC = U c := by simp [σ3, Function.update_of_ne hsd, c2]
  have ch3 : σ3.sh sC = 1 + c := by simp [σ3, ch2]
  have dh3 : σ3.sh dst = 1 + c := by simp [σ3, Function.update_of_ne hne, σ2, σ1]
  have e4 := WExec.bwd (cap := cap) sC σ3
  set σ4 := σ3.seth sC (σ3.sh sC - 1) with hσ4
  have e5 := bwd2Loop_spec cap sC dst hsd c σ4 (by simp [σ4, ch3])
    (by simp only [σ4, WState.seth_sh]; rw [Function.update_of_ne hne, dh3]; omega)
    (fun j hh1 hh2 => by simp only [σ4, WState.seth_st, c3]; exact read_U_pos c j hh1 hh2)
    (by simp only [σ4, WState.seth_st, c3]; exact read_U_zero c)
  set σ5 := (σ4.seth sC 0).seth dst (σ4.sh dst - c) with hσ5
  have e6 := WExec.fwd (cap := cap) sC σ5
  set σ6 := σ5.seth sC (σ5.sh sC + 1) with hσ6
  have e7 := WExec.bwd (cap := cap) dst σ6
  set σ7 := σ6.seth dst (σ6.sh dst - 1) with hσ7
  have v7 : σ7.val rt = 0 := by simp [σ7, σ6, σ5, σ4, σ3]; omega
  have e8 := copy1 cap rv rt t2 h1 h2 h3 v σ7 (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_of_ne h1, hv])
    v7 (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_of_ne h3.symm, ht2]) (by omega)
  set σ8 := σ7.setv rt v with hσ8
  have e9 := fwdR_spec cap dst rt v σ8 (by simp [σ8]) (by omega)
  have hs := UnaryPow.sq_ge cap
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ (by omega)
  apply wst_eq
  · intro i
    by_cases hi : i = dst
    · subst hi
      simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hne]
    · by_cases hic : i = sC
      · subst hic; simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hsd, hCh]
      · simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi, hic]
  · intro i
    by_cases hi : i = dst
    · subst hi
      simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, U]
      rw [bitsOf_eq v c hvc]; rfl
    · simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi]
  · funext x
    by_cases hx : x = rt
    · subst hx; simp [ht]
    · simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hx]
  · rfl

end Regs

/-! ## The table's copy -/

section Table
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
variable {ns nr : ℕ} (cap : ℕ)

/-- The bits of `l` from position `p`, `k` of them. -/
def readBits (l : List Bool) : ℕ → ℕ → List Bool
  | _, 0 => []
  | p, k + 1 => readTapeBit l p :: readBits l (p + 1) k

theorem readBits_app : ∀ (t pre : List Bool), readBits (pre ++ t) pre.length t.length = t
  | [], pre => rfl
  | b :: t, pre => by
    simp only [List.length_cons, readBits]
    have h1 : readTapeBit (pre ++ b :: t) pre.length = b := by
      unfold readTapeBit; simp [List.getD_eq_getElem?_getD]
    have h2 : readBits (pre ++ b :: t) (pre.length + 1) t.length = t := by
      simpa [List.append_assoc] using readBits_app t (pre ++ [b])
    rw [h1, h2]

theorem readBits_self (s : List Bool) : readBits s 0 s.length = s := by
  simpa using readBits_app s []

/-- The copy loop under a register count. -/
def tLoop (src dst : Fin (ns + 1)) (rt : Fin nr) : WM ns nr :=
  .whr rt (.seq (.dec rt) (.seq (.ifs src (.wr dst true) (.wr dst false)) (.seq (.fwd dst) (.fwd src))))

theorem tLoop_spec (src dst : Fin (ns + 1)) (hne : src ≠ dst) (rt : Fin nr) : ∀ (k : ℕ) (σ : WState ns nr),
    σ.val rt = k → k ≤ cap → σ.sh dst = (σ.st dst).length →
    WExec cap (tLoop src dst rt) σ
      ((((σ.sets dst (σ.st dst ++ readBits (σ.st src) (σ.sh src) k)).seth dst (σ.sh dst + k)).seth src
        (σ.sh src + k)).setv rt 0) (10 * k + 1)
  | 0, σ, hk, _, _ => by
    have h := WExec.whrF (cap := cap) (P := .seq (.dec rt) (.seq (.ifs src (.wr dst true) (.wr dst false))
      (.seq (.fwd dst) (.fwd src)))) (r := rt) (σ := σ) hk
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hi : i = src
      · subst hi; simp [Function.update_apply]
      · by_cases hid : i = dst
        · subst hid; simp [Function.update_apply, hi]
        · simp [Function.update_apply, hi, hid]
    · intro i; by_cases hid : i = dst
      · subst hid; simp [readBits]
      · simp [Function.update_apply, hid]
    · funext x; by_cases hx : x = rt
      · subst hx; simp [hk]
      · simp [Function.update_apply, hx]
    · rfl
  | k + 1, σ, hk, hkc, hlen => by
    have hds : dst ≠ src := fun h => hne h.symm
    set b := readTapeBit (σ.st src) (σ.sh src) with hb
    have e1 := WExec.dec (cap := cap) rt σ (by omega)
    set σ0 := σ.setv rt (σ.val rt - 1) with hσ0
    have hbr : WExec cap (.ifs src (.wr dst true) (.wr dst false)) σ0 (σ0.sets dst (σ.st dst ++ [b])) 2 := by
      cases hbv : b
      · have e := WExec.wr (cap := cap) dst false σ0
        have hf := WExec.ifsF (cap := cap) (i := src) (P := .wr dst true) (by simp [wbit, σ0, ← hb, hbv]) e
        refine WExec.cast cap hf ?_ le_rfl
        simp [σ0, hlen, wtb_end]
      · have e := WExec.wr (cap := cap) dst true σ0
        have ht := WExec.ifsT (cap := cap) (i := src) (Q := .wr dst false) (by simp [wbit, σ0, ← hb, hbv]) e
        refine WExec.cast cap ht ?_ le_rfl
        simp [σ0, hlen, wtb_end]
    set σ1 := σ0.sets dst (σ.st dst ++ [b]) with hσ1
    have e3 := WExec.fwd (cap := cap) dst σ1
    have e4 := WExec.fwd (cap := cap) src (σ1.seth dst (σ1.sh dst + 1))
    set σ2 := (σ1.seth dst (σ1.sh dst + 1)).seth src ((σ1.seth dst (σ1.sh dst + 1)).sh src + 1) with hσ2
    have hbody := WExec.seq e1 (WExec.seq hbr (WExec.seq e3 e4))
    have ih := tLoop_spec src dst hne rt k σ2 (by simp [σ2, σ1, σ0, hk]) (by omega)
      (by simp [σ2, σ1, σ0, Function.update_of_ne hds, hlen])
    have h := WExec.whrT (cap := cap) (r := rt) (by omega) hbody ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hi : i = src
      · subst hi; simp [σ2, σ1, σ0, Function.update_apply, hne, hds]; omega
      · by_cases hid : i = dst
        · subst hid; simp [σ2, σ1, σ0, Function.update_apply, hi]; omega
        · simp [σ2, σ1, σ0, Function.update_apply, hi, hid]
    · intro i
      by_cases hid : i = dst
      · subst hid; simp [σ2, σ1, σ0, Function.update_apply, hds, hne, readBits, hb]
      · simp [σ2, σ1, σ0, Function.update_apply, hid]
    · funext x; by_cases hx : x = rt
      · subst hx; simp [σ2, σ1, σ0]
      · simp [σ2, σ1, σ0, Function.update_apply, hx]
    · rfl

/-- The rewind under a register count. -/
def rLoop (src dst : Fin (ns + 1)) (rt : Fin nr) : WM ns nr := .whr rt (.seq (.dec rt) (.seq (.bwd dst) (.bwd src)))

theorem rLoop_spec (src dst : Fin (ns + 1)) (hne : src ≠ dst) (rt : Fin nr) : ∀ (k : ℕ) (σ : WState ns nr),
    σ.val rt = k → k ≤ cap →
    WExec cap (rLoop src dst rt) σ (((σ.seth dst (σ.sh dst - k)).seth src (σ.sh src - k)).setv rt 0) (7 * k + 1)
  | 0, σ, hk, _ => by
    have h := WExec.whrF (cap := cap) (P := .seq (.dec rt) (.seq (.bwd dst) (.bwd src))) (r := rt) (σ := σ) hk
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hi : i = src
      · subst hi; simp [Function.update_apply]
      · by_cases hid : i = dst
        · subst hid; simp [Function.update_apply, hi]
        · simp [Function.update_apply, hi, hid]
    · intro i; rfl
    · funext x; by_cases hx : x = rt
      · subst hx; simp [hk]
      · simp [Function.update_apply, hx]
    · rfl
  | k + 1, σ, hk, hkc => by
    have hds : dst ≠ src := fun h => hne h.symm
    have e1 := WExec.dec (cap := cap) rt σ (by omega)
    set σ0 := σ.setv rt (σ.val rt - 1) with hσ0
    have e2 := WExec.bwd (cap := cap) dst σ0
    have e3 := WExec.bwd (cap := cap) src (σ0.seth dst (σ0.sh dst - 1))
    set σ2 := (σ0.seth dst (σ0.sh dst - 1)).seth src ((σ0.seth dst (σ0.sh dst - 1)).sh src - 1) with hσ2
    have ih := rLoop_spec src dst hne rt k σ2 (by simp [σ2, σ0, hk]) (by omega)
    have h := WExec.whrT (cap := cap) (r := rt) (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hi : i = src
      · subst hi; simp [σ2, σ0, Function.update_apply, hne, hds]; omega
      · by_cases hid : i = dst
        · subst hid; simp [σ2, σ0, Function.update_apply, hi]; omega
        · simp [σ2, σ0, Function.update_apply, hi, hid]
    · intro i; rfl
    · funext x; by_cases hx : x = rt
      · subst hx; simp [σ2, σ0]
      · simp [σ2, σ0, Function.update_apply, hx]
    · rfl

/-- **The table's copy**: the source word (length in `rL`) onto a fresh tape, both heads back to `0`. -/
def tblW (src dst : Fin (ns + 1)) (rL rt t2 : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR rL rt t2) (.seq (tLoop src dst rt) (.seq (FinalPass.Hash4.wcopyR rL rt t2)
    (rLoop src dst rt)))

theorem tblW_spec (src dst : Fin (ns + 1)) (hne : src ≠ dst) (rL rt t2 : Fin nr) (h1 : rL ≠ rt) (h2 : rL ≠ t2)
    (h3 : rt ≠ t2) (σ : WState ns nr) (s : List Bool) (hs : σ.st src = s) (hsh : σ.sh src = 0) (hd : σ.st dst = [])
    (hdh : σ.sh dst = 0) (hL : σ.val rL = s.length) (ht : σ.val rt = 0) (ht2 : σ.val t2 = 0) (hcap : s.length ≤ cap) :
    WExec cap (tblW src dst rL rt t2) σ (σ.sets dst s) (17 * s.length + 2 * UnaryPow.sq cap + 5) := by
  have hds : dst ≠ src := fun h => hne h.symm
  have e1 := copy1 cap rL rt t2 h1 h2 h3 s.length σ hL ht ht2 hcap
  set σ1 := σ.setv rt s.length with hσ1
  have e2 := tLoop_spec cap src dst hne rt s.length σ1 (by simp [σ1]) hcap (by simp [σ1, hd, hdh])
  set σ2 := (((σ1.sets dst (σ1.st dst ++ readBits (σ1.st src) (σ1.sh src) s.length)).seth dst
    (σ1.sh dst + s.length)).seth src (σ1.sh src + s.length)).setv rt 0 with hσ2
  have e3 := copy1 cap rL rt t2 h1 h2 h3 s.length σ2 (by simp [σ2, σ1, Function.update_of_ne h1, hL])
    (by simp [σ2]) (by simp [σ2, σ1, Function.update_of_ne h3.symm, ht2]) hcap
  set σ3 := σ2.setv rt s.length with hσ3
  have e4 := rLoop_spec cap src dst hne rt s.length σ3 (by simp [σ3]) hcap
  have hsq := UnaryPow.sq_ge cap
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  apply wst_eq
  · intro i
    by_cases hi : i = src
    · subst hi; simp [σ3, σ2, σ1, Function.update_apply, hne, hds, hsh]
    · by_cases hid : i = dst
      · subst hid; simp [σ3, σ2, σ1, Function.update_apply, hi, hdh]
      · simp [σ3, σ2, σ1, Function.update_apply, hi, hid]
  · intro i
    by_cases hid : i = dst
    · subst hid; simp [σ3, σ2, σ1, Function.update_apply, hds, hd, hs, hsh, readBits_self]
    · simp [σ3, σ2, σ1, Function.update_apply, hid]
  · funext x; by_cases hx : x = rt
    · subst hx; simp [σ3, σ2, σ1, ht]
    · simp [σ3, σ2, σ1, Function.update_apply, hx]
  · rfl

end Table

/-! ## The install -/

section Install
open NearCubicWires.WireExponent3_5.PrimAsm
variable {ns nr : ℕ} (cap : ℕ)

/-- One stream written: `d` holds `l` at head `h`; every other stream, the registers and the cell kept. -/
def Wr (d : Fin (ns + 1)) (l : List Bool) (h : ℕ) (σ τ : WState ns nr) : Prop :=
  τ.st d = l ∧ τ.sh d = h ∧ (∀ i, i ≠ d → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell

theorem wr_sets_seth (d : Fin (ns + 1)) (l : List Bool) (h : ℕ) (σ : WState ns nr) :
    Wr d l h σ ((σ.sets d l).seth d h) :=
  ⟨by simp, by simp, fun i hi => ⟨by simp [Function.update_of_ne hi], by simp [Function.update_of_ne hi]⟩, rfl, rfl⟩

theorem wr_sets (d : Fin (ns + 1)) (l : List Bool) (h : ℕ) (σ : WState ns nr) (hh : σ.sh d = h) :
    Wr d l h σ (σ.sets d l) :=
  ⟨by simp, hh, fun i hi => ⟨by simp [Function.update_of_ne hi], rfl⟩, rfl, rfl⟩

/-- The install's targets on streams `3 … 13`: the table, the cell, `p`, the six accumulators, the log, the driver. -/
def wtI (c R p : ℕ) (a : Fin 6 → ℕ) (s : List Bool) : ℕ → List Bool
  | 3 => s
  | 4 => [false]
  | 5 => regTape c p
  | 6 => regTape c (a 0)
  | 7 => regTape c (a 1)
  | 8 => regTape c (a 2)
  | 9 => regTape c (a 3)
  | 10 => regTape c (a 4)
  | 11 => regTape c (a 5)
  | 12 => List.replicate (R + 1) false
  | _ => List.replicate R true

/-- The install's heads: `p` and the accumulators at their values, `0` elsewhere. -/
def hdI (p : ℕ) (a : Fin 6 → ℕ) : ℕ → ℕ
  | 5 => p
  | 6 => a 0
  | 7 => a 1
  | 8 => a 2
  | 9 => a 3
  | 10 => a 4
  | 11 => a 5
  | _ => 0

/-- The install's invariant once streams `3 … m−1` are written. -/
def InvI (S : Fin 14 ↪ Fin (ns + 1)) (W : ℕ → List Bool) (Hd : ℕ → ℕ) (σ : WState ns nr) (m : ℕ)
    (τ : WState ns nr) : Prop :=
  (∀ j : Fin 14, 3 ≤ j.val → j.val < m → τ.st (S j) = W j.val ∧ τ.sh (S j) = Hd j.val) ∧
  (∀ j : Fin 14, m ≤ j.val → τ.st (S j) = [] ∧ τ.sh (S j) = 0) ∧
  (∀ i, (∀ j : Fin 14, 3 ≤ j.val → i ≠ S j) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧
    τ.cell = σ.cell

theorem invI_start (S : Fin 14 ↪ Fin (ns + 1)) (W : ℕ → List Bool) (Hd : ℕ → ℕ) (σ : WState ns nr)
    (hbl : ∀ j : Fin 14, 3 ≤ j.val → σ.st (S j) = [] ∧ σ.sh (S j) = 0) : InvI S W Hd σ 3 σ :=
  ⟨fun _ h1 h2 => absurd h2 (by omega), hbl, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩

theorem invI_step {S : Fin 14 ↪ Fin (ns + 1)} {W : ℕ → List Bool} {Hd : ℕ → ℕ} {σ τ τ' : WState ns nr}
    (m : ℕ) (hm : 3 ≤ m) (k : Fin 14) (hk : k.val = m) (hI : InvI S W Hd σ m τ)
    (hW : Wr (S k) (W m) (Hd m) τ τ') : InvI S W Hd σ (m + 1) τ' := by
  obtain ⟨I1, I2, I3, I4, I5⟩ := hI
  obtain ⟨W1, W2, W3, W4, W5⟩ := hW
  refine ⟨fun j h1 h2 => ?_, fun j h1 => ?_, fun i hi => ?_, W4.trans I4, W5.trans I5⟩
  · by_cases hjk : j = k
    · subst hjk; rw [hk]; exact ⟨W1, W2⟩
    · have hne : S j ≠ S k := fun h => hjk (S.injective h)
      have hjv : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rw [(W3 _ hne).1, (W3 _ hne).2]; exact I1 j h1 (by omega)
  · have hne : S j ≠ S k := fun h => by have := congrArg Fin.val (S.injective h); omega
    rw [(W3 _ hne).1, (W3 _ hne).2]; exact I2 j (by omega)
  · have hne : i ≠ S k := hi k (by omega)
    rw [(W3 _ hne).1, (W3 _ hne).2]; exact I3 i hi

theorem invI_low {S : Fin 14 ↪ Fin (ns + 1)} {W : ℕ → List Bool} {Hd : ℕ → ℕ} {σ τ : WState ns nr} {m : ℕ}
    (hI : InvI S W Hd σ m τ) (k : Fin 14) (hk : k.val < 3) : τ.st (S k) = σ.st (S k) ∧ τ.sh (S k) = σ.sh (S k) :=
  hI.2.2.1 (S k) (fun j hj h => by have := congrArg Fin.val (S.injective h); omega)

/-- One register written from the ruler `U c` on `S 0` (the install's step on stream `k`). -/
theorem regTW_inv {S : Fin 14 ↪ Fin (ns + 1)} {W : ℕ → List Bool} {Hd : ℕ → ℕ} {σ τ : WState ns nr}
    (m : ℕ) (hm : 3 ≤ m) (k : Fin 14) (hk : k.val = m) (hI : InvI S W Hd σ m τ) (rv rt t2 : Fin nr) (h1 : rv ≠ rt)
    (h2 : rv ≠ t2) (h3 : rt ≠ t2) (c v : ℕ) (hC : σ.st (S 0) = U c) (hCh : σ.sh (S 0) = 1) (hv : σ.val rv = v)
    (ht : σ.val rt = 0) (ht2 : σ.val t2 = 0) (hvc : v ≤ c) (hvcap : v ≤ cap) (hW : W m = regTape c v)
    (hH : Hd m = v) :
    ∃ τ', WExec cap (regTW (S k) (S 0) rv rt t2) τ τ' (20 * c + 5 * v + 2 * UnaryPow.sq cap + 30) ∧
      InvI S W Hd σ (m + 1) τ' := by
  have hk0 : S k ≠ S 0 := fun h => by
    have := congrArg Fin.val (S.injective h)
    change k.val = 0 at this
    omega
  have c0 := invI_low hI 0 (by decide)
  have bk := hI.2.1 k (by omega)
  have hv' := hI.2.2.2.1
  refine ⟨_, regTW_spec cap (S k) (S 0) hk0 rv rt t2 h1 h2 h3 τ c v (c0.1.trans hC) (c0.2.trans hCh) bk.1 bk.2
    (by rw [hv']; exact hv) (by rw [hv']; exact ht) (by rw [hv']; exact ht2) hvc hvcap, ?_⟩
  exact invI_step m hm k hk hI (by rw [hW, hH]; exact wr_sets_seth (S k) (regTape c v) v τ)

/-- **The install's body**: the table, the cell, `p`, the accumulators, the log, the driver (streams `3 … 13`). -/
def instBody (S : Fin 14 ↪ Fin (ns + 1)) (Rg : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (tblW (S 2) (S 3) (Rg 0) (Rg 8) (Rg 9)) (.seq (.wr (S 4) false)
  (.seq (regTW (S 5) (S 0) (Rg 1) (Rg 8) (Rg 9)) (.seq (regTW (S 6) (S 0) (Rg 2) (Rg 8) (Rg 9))
  (.seq (regTW (S 7) (S 0) (Rg 3) (Rg 8) (Rg 9)) (.seq (regTW (S 8) (S 0) (Rg 4) (Rg 8) (Rg 9))
  (.seq (regTW (S 9) (S 0) (Rg 5) (Rg 8) (Rg 9)) (.seq (regTW (S 10) (S 0) (Rg 6) (Rg 8) (Rg 9))
  (.seq (regTW (S 11) (S 0) (Rg 7) (Rg 8) (Rg 9)) (.seq (zerosW (S 1) (S 12)) (onesW (S 1) (S 13)))))))))))

/-- The body's cost. -/
def bodyCost (c R L sqc : ℕ) : ℕ := 17 * L + 24 * R + 175 * c + 16 * sqc + 250

/-- **The install's body**: streams `S 3 … S 13` (blank at entry) receive the table (copied from `S 2`, its length in
`Rg 0`), the cell `[false]`, `p` (`Rg 1`) and the six accumulators (`Rg 2 … Rg 7`) as registers of capacity `c` (the
ruler `U c` on `S 0`), the log `0^{R+1}` and the driver `1^R` (the ruler `U R` on `S 1`); every other stream, the
registers and the cell are kept. -/
theorem instBody_spec (S : Fin 14 ↪ Fin (ns + 1)) (Rg : Fin 10 ↪ Fin nr) (σ : WState ns nr) (c R p : ℕ)
    (a : Fin 6 → ℕ) (s : List Bool) (h0 : σ.st (S 0) = U c) (h0h : σ.sh (S 0) = 1) (h1 : σ.st (S 1) = U R)
    (h1h : σ.sh (S 1) = 1) (h2 : σ.st (S 2) = s) (h2h : σ.sh (S 2) = 0)
    (hbl : ∀ j : Fin 14, 3 ≤ j.val → σ.st (S j) = [] ∧ σ.sh (S j) = 0)
    (hL : σ.val (Rg 0) = s.length) (hp : σ.val (Rg 1) = p) (ha0 : σ.val (Rg 2) = a 0) (ha1 : σ.val (Rg 3) = a 1)
    (ha2 : σ.val (Rg 4) = a 2) (ha3 : σ.val (Rg 5) = a 3) (ha4 : σ.val (Rg 6) = a 4) (ha5 : σ.val (Rg 7) = a 5)
    (ht : σ.val (Rg 8) = 0) (ht2 : σ.val (Rg 9) = 0) (hpc : p ≤ c) (hac : ∀ i, a i ≤ c) (hpW : p ≤ cap)
    (haW : ∀ i, a i ≤ cap) (hsc : s.length ≤ cap) :
    ∃ τ, WExec cap (instBody S Rg) σ τ (bodyCost c R s.length (UnaryPow.sq cap)) ∧
      (∀ j : Fin 14, 3 ≤ j.val → τ.st (S j) = wtI c R p a s j.val ∧ τ.sh (S j) = hdI p a j.val) ∧
      (∀ i, (∀ j : Fin 14, 3 ≤ j.val → i ≠ S j) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧
      τ.cell = σ.cell := by
  have hS : ∀ i j : Fin 14, i ≠ j → S i ≠ S j := fun i j h => S.injective.ne h
  have hR : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => Rg.injective.ne h
  have h89 : Rg 8 ≠ Rg 9 := hR 8 9 (by decide)
  have I3 : InvI S (wtI c R p a s) (hdI p a) σ 3 σ := invI_start S _ _ σ hbl
  obtain ⟨τ4, e3, I4⟩ : ∃ τ', WExec cap (tblW (S 2) (S 3) (Rg 0) (Rg 8) (Rg 9)) σ τ'
      (17 * s.length + 2 * UnaryPow.sq cap + 5) ∧ InvI S (wtI c R p a s) (hdI p a) σ 4 τ' :=
    ⟨_, tblW_spec cap (S 2) (S 3) (hS 2 3 (by decide)) (Rg 0) (Rg 8) (Rg 9) (hR 0 8 (by decide))
      (hR 0 9 (by decide)) h89 σ s h2 h2h (hbl 3 (by decide)).1 (hbl 3 (by decide)).2 hL ht ht2 hsc,
      invI_step 3 le_rfl 3 rfl I3 (wr_sets (S 3) s 0 σ (hbl 3 (by decide)).2)⟩
  obtain ⟨τ5, e4, I5⟩ : ∃ τ', WExec cap (.wr (S 4) false) τ4 τ' 1 ∧ InvI S (wtI c R p a s) (hdI p a) σ 5 τ' :=
    ⟨_, cellW_spec cap (S 4) τ4 (I4.2.1 4 (by decide)).1 (I4.2.1 4 (by decide)).2,
      invI_step 4 (by omega) 4 rfl I4 (wr_sets (S 4) [false] 0 τ4 (I4.2.1 4 (by decide)).2)⟩
  obtain ⟨τ6, e5, I6⟩ := regTW_inv cap 5 (by omega) 5 rfl I5 (Rg 1) (Rg 8) (Rg 9) (hR 1 8 (by decide))
    (hR 1 9 (by decide)) h89 c p h0 h0h hp ht ht2 hpc hpW rfl rfl
  obtain ⟨τ7, e6, I7⟩ := regTW_inv cap 6 (by omega) 6 rfl I6 (Rg 2) (Rg 8) (Rg 9) (hR 2 8 (by decide))
    (hR 2 9 (by decide)) h89 c (a 0) h0 h0h ha0 ht ht2 (hac 0) (haW 0) rfl rfl
  obtain ⟨τ8, e7, I8⟩ := regTW_inv cap 7 (by omega) 7 rfl I7 (Rg 3) (Rg 8) (Rg 9) (hR 3 8 (by decide))
    (hR 3 9 (by decide)) h89 c (a 1) h0 h0h ha1 ht ht2 (hac 1) (haW 1) rfl rfl
  obtain ⟨τ9, e8, I9⟩ := regTW_inv cap 8 (by omega) 8 rfl I8 (Rg 4) (Rg 8) (Rg 9) (hR 4 8 (by decide))
    (hR 4 9 (by decide)) h89 c (a 2) h0 h0h ha2 ht ht2 (hac 2) (haW 2) rfl rfl
  obtain ⟨τ10, e9, I10⟩ := regTW_inv cap 9 (by omega) 9 rfl I9 (Rg 5) (Rg 8) (Rg 9) (hR 5 8 (by decide))
    (hR 5 9 (by decide)) h89 c (a 3) h0 h0h ha3 ht ht2 (hac 3) (haW 3) rfl rfl
  obtain ⟨τ11, e10, I11⟩ := regTW_inv cap 10 (by omega) 10 rfl I10 (Rg 6) (Rg 8) (Rg 9) (hR 6 8 (by decide))
    (hR 6 9 (by decide)) h89 c (a 4) h0 h0h ha4 ht ht2 (hac 4) (haW 4) rfl rfl
  obtain ⟨τ12, e11, I12⟩ := regTW_inv cap 11 (by omega) 11 rfl I11 (Rg 7) (Rg 8) (Rg 9) (hR 7 8 (by decide))
    (hR 7 9 (by decide)) h89 c (a 5) h0 h0h ha5 ht ht2 (hac 5) (haW 5) rfl rfl
  obtain ⟨τ13, e12, I13⟩ : ∃ τ', WExec cap (zerosW (S 1) (S 12)) τ12 τ' (12 * R + 9) ∧
      InvI S (wtI c R p a s) (hdI p a) σ 13 τ' :=
    ⟨_, zerosW_spec cap (S 1) (S 12) (hS 1 12 (by decide)) τ12 R ((invI_low I12 1 (by decide)).1.trans h1)
      ((invI_low I12 1 (by decide)).2.trans h1h) (I12.2.1 12 (by decide)).1 (I12.2.1 12 (by decide)).2,
      invI_step 12 (by omega) 12 rfl I12 (wr_sets_seth (S 12) (List.replicate (R + 1) false) 0 τ12)⟩
  obtain ⟨τ14, e13, I14⟩ : ∃ τ', WExec cap (onesW (S 1) (S 13)) τ13 τ' (12 * R + 7) ∧
      InvI S (wtI c R p a s) (hdI p a) σ 14 τ' :=
    ⟨_, onesW_spec cap (S 1) (S 13) (hS 1 13 (by decide)) τ13 R ((invI_low I13 1 (by decide)).1.trans h1)
      ((invI_low I13 1 (by decide)).2.trans h1h) (I13.2.1 13 (by decide)).1 (I13.2.1 13 (by decide)).2,
      invI_step 13 (by omega) 13 rfl I13 (wr_sets_seth (S 13) (List.replicate R true) 0 τ13)⟩
  have a0 := hac 0
  have a1 := hac 1
  have a2 := hac 2
  have a3 := hac 3
  have a4 := hac 4
  have a5 := hac 5
  refine ⟨τ14, WExec.cast cap (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 (WExec.seq e8
    (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 e13)))))))))) rfl ?_,
    fun j hj => I14.1 j hj j.isLt, I14.2.2.1, I14.2.2.2.1, I14.2.2.2.2⟩
  unfold bodyCost
  omega

end Install

/-! ## The table's rewind, then the install -/

section Install2
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
variable {ns nr : ℕ} (cap : ℕ)

/-- The backward count: `v` steps of `dst` back, counting `rt` down. -/
def bwdR (dst : Fin (ns + 1)) (rt : Fin nr) : WM ns nr := .whr rt (.seq (.dec rt) (.bwd dst))

theorem bwdR_spec (dst : Fin (ns + 1)) (rt : Fin nr) : ∀ (v : ℕ) (σ : WState ns nr), σ.val rt = v → v ≤ cap →
    WExec cap (bwdR dst rt) σ ((σ.setv rt 0).seth dst (σ.sh dst - v)) (5 * v + 1)
  | 0, σ, hv, _ => by
    have h := WExec.whrF (cap := cap) (P := .seq (.dec rt) (.bwd dst)) (r := rt) (σ := σ) hv
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = dst
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · funext x; by_cases hx : x = rt
      · subst hx; simp [hv]
      · simp [Function.update_apply, hx]
    · rfl
  | v + 1, σ, hv, hvc => by
    have e1 := WExec.dec (cap := cap) rt σ (by omega)
    have e2 := WExec.bwd (cap := cap) dst (σ.setv rt (σ.val rt - 1))
    have ih := bwdR_spec dst rt v ((σ.setv rt (σ.val rt - 1)).seth dst ((σ.setv rt (σ.val rt - 1)).sh dst - 1))
      (by simp [hv]) (by omega)
    have h := WExec.whrT (cap := cap) (r := rt) (by omega) (WExec.seq e1 e2) ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = dst
      · subst hi; simp; omega
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · funext x; by_cases hx : x = rt
      · subst hx; simp
      · simp [Function.update_apply, hx]
    · rfl

/-- The rewind of a written stream whose length is in `rL` (its head at its end). -/
def rewW (src : Fin (ns + 1)) (rL rt t2 : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR rL rt t2) (bwdR src rt)

theorem rewW_spec (src : Fin (ns + 1)) (rL rt t2 : Fin nr) (h1 : rL ≠ rt) (h2 : rL ≠ t2) (h3 : rt ≠ t2)
    (σ : WState ns nr) (L : ℕ) (hL : σ.val rL = L) (ht : σ.val rt = 0) (ht2 : σ.val t2 = 0) (hsh : σ.sh src = L)
    (hcap : L ≤ cap) : WExec cap (rewW src rL rt t2) σ (σ.seth src 0) (UnaryPow.sq cap + 5 * L + 2) := by
  have e1 := copy1 cap rL rt t2 h1 h2 h3 L σ hL ht ht2 hcap
  have e2 := bwdR_spec cap src rt L (σ.setv rt L) (by simp) hcap
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply wst_eq
  · intro i; by_cases hi : i = src
    · subst hi; simp [hsh]
    · simp [Function.update_apply, hi]
  · intro i; rfl
  · funext x; by_cases hx : x = rt
    · subst hx; simp [ht]
    · simp [Function.update_apply, hx]
  · rfl

/-- **The install program**: rewind the table's source (its length in `Rg 0`), then the install's body. -/
def installW (S : Fin 14 ↪ Fin (ns + 1)) (Rg : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (rewW (S 2) (Rg 0) (Rg 8) (Rg 9)) (instBody S Rg)

/-- The install's cost. -/
def installCost (c R L sqc : ℕ) : ℕ := 22 * L + 24 * R + 175 * c + 17 * sqc + 260

/-- **The install**: the table's source `S 2` (the table writer's output, head at its end, its length in `Rg 0`) is
rewound; streams `S 3 … S 13` (blank at entry) receive the table, the cell `[false]`, `p` (`Rg 1`) and the six
accumulators (`Rg 2 … Rg 7`) as registers of capacity `c` (the ruler `U c` on `S 0`), the log `0^{R+1}` and the driver
`1^R` (the ruler `U R` on `S 1`); every other stream, the registers and the cell are kept. -/
theorem installW_spec (S : Fin 14 ↪ Fin (ns + 1)) (Rg : Fin 10 ↪ Fin nr) (σ : WState ns nr) (c R p : ℕ)
    (a : Fin 6 → ℕ) (s : List Bool) (h0 : σ.st (S 0) = U c) (h0h : σ.sh (S 0) = 1) (h1 : σ.st (S 1) = U R)
    (h1h : σ.sh (S 1) = 1) (h2 : σ.st (S 2) = s) (h2h : σ.sh (S 2) = s.length)
    (hbl : ∀ j : Fin 14, 3 ≤ j.val → σ.st (S j) = [] ∧ σ.sh (S j) = 0)
    (hL : σ.val (Rg 0) = s.length) (hp : σ.val (Rg 1) = p) (ha0 : σ.val (Rg 2) = a 0) (ha1 : σ.val (Rg 3) = a 1)
    (ha2 : σ.val (Rg 4) = a 2) (ha3 : σ.val (Rg 5) = a 3) (ha4 : σ.val (Rg 6) = a 4) (ha5 : σ.val (Rg 7) = a 5)
    (ht : σ.val (Rg 8) = 0) (ht2 : σ.val (Rg 9) = 0) (hpc : p ≤ c) (hac : ∀ i, a i ≤ c) (hpW : p ≤ cap)
    (haW : ∀ i, a i ≤ cap) (hsc : s.length ≤ cap) :
    ∃ τ, WExec cap (installW S Rg) σ τ (installCost c R s.length (UnaryPow.sq cap)) ∧
      (∀ j : Fin 14, 3 ≤ j.val → τ.st (S j) = wtI c R p a s j.val ∧ τ.sh (S j) = hdI p a j.val) ∧
      τ.st (S 2) = s ∧ τ.sh (S 2) = 0 ∧
      (∀ i, (∀ j : Fin 14, 2 ≤ j.val → i ≠ S j) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧
      τ.cell = σ.cell := by
  have hS : ∀ i j : Fin 14, i ≠ j → S i ≠ S j := fun i j h => S.injective.ne h
  have hR : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => Rg.injective.ne h
  have e0 := rewW_spec cap (S 2) (Rg 0) (Rg 8) (Rg 9) (hR 0 8 (by decide)) (hR 0 9 (by decide)) (hR 8 9 (by decide))
    σ s.length hL ht ht2 h2h hsc
  have n2 : ∀ j : Fin 14, 3 ≤ j.val → S j ≠ S 2 := fun j hj h => by
    have := congrArg Fin.val (S.injective h)
    change j.val = 2 at this
    omega
  obtain ⟨τ, e, hA, hB, hV, hC⟩ := instBody_spec cap S Rg (σ.seth (S 2) 0) c R p a s h0
    (by simp [Function.update_of_ne (hS 0 2 (by decide)), h0h]) h1
    (by simp [Function.update_of_ne (hS 1 2 (by decide)), h1h]) h2 (by simp)
    (fun j hj => ⟨(hbl j hj).1, by simp [Function.update_of_ne (n2 j hj), (hbl j hj).2]⟩)
    hL hp ha0 ha1 ha2 ha3 ha4 ha5 ht ht2 hpc hac hpW haW hsc
  have o2 : ∀ j : Fin 14, 3 ≤ j.val → S 2 ≠ S j := fun j hj h => n2 j hj h.symm
  refine ⟨τ, WExec.cast cap (WExec.seq e0 e) rfl ?_, hA, ?_, ?_, fun i hi => ?_, hV, hC⟩
  · unfold installCost bodyCost
    omega
  · rw [(hB (S 2) o2).1]; exact h2
  · rw [(hB (S 2) o2).2]; simp
  · have hi3 : ∀ j : Fin 14, 3 ≤ j.val → i ≠ S j := fun j hj => hi j (by omega)
    have hi2 : i ≠ S 2 := hi 2 (by decide)
    rw [(hB i hi3).1, (hB i hi3).2]
    exact ⟨rfl, by simp [Function.update_of_ne hi2]⟩

end Install2

end NearCubicWires.WireExponent3_5.UnionMachine.FrontInstall
