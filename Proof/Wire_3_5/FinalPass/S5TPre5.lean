import Proof.Wire_3_5.FinalPass.S5TTailB

/-! # S5-THR, part 20: the prelude on the scrub's layout, with a padded count base (P3:3170-3181)

The THR half runs its main stage under base's scrub (`BlockScrub`: the stage's tapes, then a log and a driver
`1^R`), and the scrub needs the stage's cost below `R` at EVERY request. So the count base is padded by a machine
constant `c0`: `y = |u| + 1 + c0`, the powers `xs j = sent (y^{j+1})`, the count `C = 1^W`, `W = y^{D+1}`; and the
count lands on the scrub's DRIVER, the fill's marker on the scrub's LOG.

* `emitN_spec`, `padW` / **`padW_spec`** (a sentinel word padded by `c0` ones, head back at `0`);
* `preW2` / **`preW2_spec`** (the count program with the padded base), `preSt2`;
* the count program's own layout (`sI2 sT2 sP2 sC2 sxs2`), `preSub2`, `σIn2`, `τOut2`, `preSub2_spec`;
* `cellP2`, `regSel2`, `preSlots2` (+ inj), `preM2`, `A02`, `σ02`, **`pre_step2`**: from the final pass's entry bank
  to `Scrub.bank (wenc (2W+2) σ02).A W (2W+3)`, every head at `0`.

Paper quantity of the main type: the front's register capacity `2W + 2` with `W = (|fpIn| + 1 + c0)^{D+1}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj sTape_ne_c sTape_ne_r cTape_ne_r wslot
  wslot_s wslot_c wenc_A_c wenc_H_c)

section Words
variable {ns nr : ℕ} (cap : ℕ)

/-- `k` ones appended to `O`. -/
def emitN (O : Fin (ns + 1)) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (emit1 O true) (emitN O k)

theorem emitN_spec (O : Fin (ns + 1)) : ∀ (k : ℕ) (σ : WState ns nr), σ.sh O = (σ.st O).length →
    WExec cap (emitN O k) σ (appW σ O (List.replicate k true)) (4 * k)
  | 0, σ, hO => by
    rw [List.replicate_zero, appW_nil σ O hO]
    exact WExec.cast cap (WExec.skip σ) rfl (by omega)
  | k + 1, σ, hO => by
    have e1 := emit1_spec cap O true σ hO
    have ih := emitN_spec O k (appW σ O [true]) (by simp)
    rw [appW_appW] at ih
    exact WExec.cast cap (WExec.seq e1 ih) (by rw [List.replicate_succ]; rfl) (by omega)

/-- A sentinel word padded by `c0` ones, its head back at `0`. -/
def padW (P : Fin (ns + 1)) (c0 : ℕ) : WM ns nr := .seq (fwdEnd P) (.seq (emitN P c0) (rewSent P))

theorem sent_add (b c : ℕ) : sent b ++ List.replicate c true = sent (b + c) := by
  show false :: (List.replicate b true ++ List.replicate c true) = false :: List.replicate (b + c) true
  rw [List.replicate_add]

theorem padW_spec (P : Fin (ns + 1)) (c0 b : ℕ) (σ : WState ns nr) (hs : σ.st P = sent b) (hp : σ.sh P = 0) :
    WExec cap (padW P c0) σ (σ.sets P (sent (b + c0))) (3 * b + 3 + 1 + (4 * c0 + 1 + (3 * (b + c0) + 3))) := by
  have e1 := fwdEnd_spec cap P b σ hs hp
  have e2 := emitN_spec cap P c0 (σ.seth P (b + 1)) (by simp [hs, sent_length])
  have e3 := rewSent_spec cap P (b + c0) (appW (σ.seth P (b + 1)) P (List.replicate c0 true))
    (by simp [hs, sent_add]) (by simp [hs, sent_length]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  apply WState.eq
  · funext i; by_cases hi : i = P
    · subst hi; simp [hp]
    · simp [Function.update_apply, hi]
  · funext i; by_cases hi : i = P
    · subst hi; simp [hs, sent_add]
    · simp [Function.update_apply, hi]
  · rfl
  · rfl

theorem sets_sets' (σ : WState ns nr) (i : Fin (ns + 1)) (x y : List Bool) : (σ.sets i x).sets i y = σ.sets i y :=
  WState.eq rfl (by funext j; by_cases h : j = i <;> simp [Function.update_apply, h]) rfl rfl

/-- **The count program with a padded base**: template, its padded copy, the powers, the count. -/
def preW2 (I T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (D c0 : ℕ) : WM ns nr :=
  .seq (lenT I T) (.seq (sentCopy T P) (.seq (padW P c0) (.seq (sentCopy P (xs 0))
    (.seq (chainW xs P D) (plainCopy (xs D) C)))))

/-- The padded count program's exit state. -/
def preSt2 (σ : WState ns nr) (T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (b c0 D : ℕ) : WState ns nr :=
  (chainSt (((σ.sets T (sent b)).sets P (sent (b + c0))).sets (xs 0) (sent (b + c0))) xs (b + c0) D).sets C
    (List.replicate ((b + c0) ^ (D + 1)) true)

/-- The padded count program's cost. -/
def preCost2 (b c0 D : ℕ) : ℕ :=
  (16 * (b - 1) + 20) + 1 + ((13 * b + 15) + 1 + ((3 * b + 3 + 1 + (4 * c0 + 1 + (3 * (b + c0) + 3))) + 1 +
    ((13 * (b + c0) + 15) + 1 + (chainCost (b + c0) D + 1 + (12 * (b + c0) ^ (D + 1) + 7)))))

theorem preW2_spec (I T P C : Fin (ns + 1)) (xs : ℕ → Fin (ns + 1)) (D c0 : ℕ)
    (hxs : ∀ i j, i ≤ D → j ≤ D → xs i = xs j → i = j)
    (hIT : I ≠ T) (hTP : T ≠ P) (hPC : P ≠ C) (hTC : T ≠ C) (hPx : ∀ j, j ≤ D → xs j ≠ P)
    (hTx : ∀ j, j ≤ D → xs j ≠ T) (hCx : ∀ j, j ≤ D → xs j ≠ C)
    (u : List Bool) (σ : WState ns nr) (hI : σ.st I = frame u) (hIh : σ.sh I = 0) (hT : σ.st T = [])
    (hTh : σ.sh T = 0) (hP : σ.st P = []) (hPh : σ.sh P = 0) (hC : σ.st C = []) (hCh : σ.sh C = 0)
    (hx : ∀ j, j ≤ D → σ.st (xs j) = []) (hxh : ∀ j, j ≤ D → σ.sh (xs j) = 0) :
    WExec cap (preW2 I T P C xs D c0) σ (preSt2 σ T P C xs (u.length + 1) c0 D) (preCost2 (u.length + 1) c0 D) := by
  have e1 := lenT_spec cap I T hIT u σ hI hIh hT hTh
  have e2 := sentCopy_spec cap T P hTP (u.length + 1) (σ.sets T (sent (u.length + 1))) (by simp) (by simpa using hTh)
    (by simp [Function.update_apply, Ne.symm hTP, hP]) (by simpa using hPh)
  have e3 := padW_spec cap P c0 (u.length + 1) ((σ.sets T (sent (u.length + 1))).sets P (sent (u.length + 1)))
    (by simp) (by simpa using hPh)
  rw [sets_sets'] at e3
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = (σ.sets T (sent (u.length + 1))).sets P (sent (u.length + 1 + c0)) := ⟨_, rfl⟩
  rw [← hσ2] at e3
  have e4 := sentCopy_spec cap P (xs 0) (Ne.symm (hPx 0 (by omega))) (u.length + 1 + c0) σ2
    (by rw [hσ2]; simp) (by rw [hσ2]; simpa using hPh)
    (by rw [hσ2]; simp [Function.update_apply, hPx 0 (by omega), hTx 0 (by omega), hx 0 (by omega)])
    (by rw [hσ2]; simpa using hxh 0 (by omega))
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.sets (xs 0) (sent (u.length + 1 + c0)) := ⟨_, rfl⟩
  rw [← hσ3] at e4
  have e5 := chainW_spec cap xs P D hxs hPx (u.length + 1 + c0) σ3 (by rw [hσ3]; simp)
    (by rw [hσ3, hσ2]; simp [Function.update_apply, Ne.symm (hPx 0 (by omega))])
    (by rw [hσ3, hσ2]; simpa using hPh)
    (fun j hj => by rw [hσ3, hσ2]; simpa using hxh j hj) D le_rfl
    (fun j h1 h2 => by
      rw [hσ3, hσ2]; simp only [WState.sets_st]
      rw [Function.update_of_ne (fun e => by have := hxs _ _ h2 (by omega) e; omega),
        Function.update_of_ne (hPx j h2), Function.update_of_ne (hTx j h2)]
      exact hx j h2)
  have hDs : (chainSt σ3 xs (u.length + 1 + c0) D).st (xs D) = sent ((u.length + 1 + c0) ^ (D + 1)) := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; rw [chainSt, hσ3]; simp
    · exact chainSt_st_self xs D hxs σ3 (u.length + 1 + c0) D D le_rfl hD le_rfl
  have e6 := plainCopy_spec cap (xs D) C (hCx D le_rfl) ((u.length + 1 + c0) ^ (D + 1))
    (chainSt σ3 xs (u.length + 1 + c0) D) hDs (by rw [chainSt_sh, hσ3, hσ2]; simpa using hxh D le_rfl)
    (by
      rw [chainSt_st_ne xs σ3 (u.length + 1 + c0) C D (fun j _ h2 => hCx j h2), hσ3, hσ2]
      simp [Function.update_apply, Ne.symm (hCx 0 (by omega)), Ne.symm hTC, Ne.symm hPC, hC])
    (by rw [chainSt_sh, hσ3, hσ2]; simpa using hCh)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · rw [hσ3, hσ2]; rfl
  · unfold preCost2; simp only [Nat.add_sub_cancel]; omega

end Words

/-! ## The count program's own layout -/

/-- Its input stream. -/
def sI2 (D : ℕ) : Fin (D + 5) := ⟨0, by omega⟩
/-- Its template. -/
def sT2 (D : ℕ) : Fin (D + 5) := ⟨1, by omega⟩
/-- Its padded template. -/
def sP2 (D : ℕ) : Fin (D + 5) := ⟨2, by omega⟩
/-- Its count. -/
def sC2 (D : ℕ) : Fin (D + 5) := ⟨3, by omega⟩
/-- Its powers `xs j = 4 + j` (`j ≤ D`). -/
def sxs2 (D j : ℕ) : Fin (D + 5) := if h : 4 + j < D + 5 then ⟨4 + j, h⟩ else ⟨0, by omega⟩

theorem sxs2_val (D j : ℕ) (hj : j ≤ D) : (sxs2 D j).val = 4 + j := by unfold sxs2; rw [dif_pos (by omega)]

/-- Its entry state. -/
def σIn2 (D : ℕ) (u : List Bool) : WState (D + 4) 0 :=
  ⟨fun _ => 0, fun i => if i = sI2 D then frame u else [], Fin.elim0, false⟩

end NearCubicWires.WireExponent3_5.FinalPass.S5T
