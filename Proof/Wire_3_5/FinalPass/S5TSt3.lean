import Proof.Wire_3_5.FinalPass.S5TPost

/-! # S5-THR, part 29: the prelude's exit, read off (P3:3170-3181)

The prelude's exit state `σ03` on the THR half's layout (`fs2`): the input `frame u`, the template `sent(|u|+1)`,
the padded template `sent y`, the powers `sent(y^{j+1})` (`j < D`), the top power `W + 1` zeros, every other stream
blank; heads, registers `0`, the cell `false` (`y = |u| + 1 + c0`, `W = y^{D+1}`).

* `τOut3_I/T/P/xs/xsD` (the count program's exit streams); **`σ03_in/tm/pad/xs/xsD/blank`**, `σ03_sh`, `σ03_val`.

Paper quantity: none beyond the prelude (the front's register capacity `2W + 2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm

section Out3
variable (D c0 : ℕ) (u : List Bool)

theorem sxs2_ne (j : ℕ) (hj : j ≤ D) : sxs2 D j ≠ sI2 D ∧ sxs2 D j ≠ sT2 D ∧ sxs2 D j ≠ sP2 D ∧ sxs2 D j ≠ sC2 D := by
  have hv := sxs2_val D j hj
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    (have h := congrArg Fin.val e; rw [hv] at h; simp only [sI2, sT2, sP2, sC2, Fin.val_mk] at h; omega)

theorem sxs2_inj (i j : ℕ) (hi : i ≤ D) (hj : j ≤ D) (e : sxs2 D i = sxs2 D j) : i = j := by
  have := congrArg Fin.val e; rw [sxs2_val D i hi, sxs2_val D j hj] at this; omega

theorem τOut3_other (k : Fin (D + 5)) (hT : k ≠ sT2 D) (hP : k ≠ sP2 D) (hC : k ≠ sC2 D)
    (hx : ∀ j, j ≤ D → sxs2 D j ≠ k) : (τOut3 D c0 u).st k = (σIn2 D u).st k := by
  unfold τOut3 preSt3 preSt2
  simp only [WState.sets_st]
  rw [Function.update_of_ne (Ne.symm (hx D le_rfl)), Function.update_of_ne hC,
    chainSt_st_ne _ _ _ k D (fun j _ h2 => hx j h2)]
  simp only [WState.sets_st]
  rw [Function.update_of_ne (Ne.symm (hx 0 (by omega))), Function.update_of_ne hP, Function.update_of_ne hT]

theorem τOut3_I : (τOut3 D c0 u).st (sI2 D) = frame u := by
  have ne : ∀ {a b : Fin (D + 5)}, a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  rw [τOut3_other D c0 u _ (ne (by simp [sI2, sT2])) (ne (by simp [sI2, sP2])) (ne (by simp [sI2, sC2]))
    (fun j hj => (sxs2_ne D j hj).1)]
  show (if sI2 D = sI2 D then frame u else []) = frame u
  rw [if_pos rfl]

theorem τOut3_T : (τOut3 D c0 u).st (sT2 D) = sent (u.length + 1) := by
  have ne : ∀ {a b : Fin (D + 5)}, a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  unfold τOut3 preSt3 preSt2
  simp only [WState.sets_st]
  rw [Function.update_of_ne (fun e => (sxs2_ne D D le_rfl).2.1 e.symm), Function.update_of_ne (ne (by simp [sT2, sC2])),
    chainSt_st_ne _ _ _ _ D (fun j _ h2 => (sxs2_ne D j h2).2.1)]
  simp only [WState.sets_st]
  rw [Function.update_of_ne (fun e => (sxs2_ne D 0 (by omega)).2.1 e.symm), Function.update_of_ne (ne (by simp [sT2, sP2]))]
  simp

theorem τOut3_P : (τOut3 D c0 u).st (sP2 D) = sent (u.length + 1 + c0) := by
  have ne : ∀ {a b : Fin (D + 5)}, a.val ≠ b.val → a ≠ b := fun h e => h (congrArg Fin.val e)
  unfold τOut3 preSt3 preSt2
  simp only [WState.sets_st]
  rw [Function.update_of_ne (fun e => (sxs2_ne D D le_rfl).2.2.1 e.symm), Function.update_of_ne (ne (by simp [sP2, sC2])),
    chainSt_st_ne _ _ _ _ D (fun j _ h2 => (sxs2_ne D j h2).2.2.1)]
  simp only [WState.sets_st]
  rw [Function.update_of_ne (fun e => (sxs2_ne D 0 (by omega)).2.2.1 e.symm)]
  simp

theorem τOut3_xs (j : ℕ) (hj : j < D) :
    (τOut3 D c0 u).st (sxs2 D j) = sent ((u.length + 1 + c0) ^ (j + 1)) := by
  unfold τOut3 preSt3 preSt2
  simp only [WState.sets_st]
  rw [Function.update_of_ne (fun e => by have := sxs2_inj D j D (by omega) le_rfl e; omega),
    Function.update_of_ne (sxs2_ne D j (by omega)).2.2.2]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [chainSt_st_ne _ _ _ _ D (fun k h1 h2 e => by have := sxs2_inj D k 0 h2 (by omega) e; omega)]
    simp
  · exact chainSt_st_self (sxs2 D) D (sxs2_inj D) _ _ D j le_rfl h0 (by omega)

theorem τOut3_xsD : (τOut3 D c0 u).st (sxs2 D D) = List.replicate ((u.length + 1 + c0) ^ (D + 1) + 1) false := by
  unfold τOut3 preSt3; simp

end Out3

section St3
variable (D x6 xt c0 : ℕ) (u : List Bool)

theorem σ03_fs (k : Fin (D + 5)) :
    (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st (fs2 D x6 xt k) = if k = sC2 D then [] else (τOut3 D c0 u).st k := by
  show install (fs2 D x6 xt) (fun _ => []) (fun k => if k = sC2 D then [] else (τOut3 D c0 u).st k)
    (fs2 D x6 xt k) = _
  rw [install_slot _ (fs2_inj D x6 xt)]

theorem σ03_out (i : Fin (nsL D x6 xt + 1)) (hi : ∀ k, fs2 D x6 xt k ≠ i) :
    (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st i = [] := by
  show install (fs2 D x6 xt) (fun _ => []) (fun k => if k = sC2 D then [] else (τOut3 D c0 u).st k) i = _
  rw [install_other _ _ _ _ hi]

theorem σ03_in : (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st (sIn D x6 xt) = frame u := by
  rw [show sIn D x6 xt = fs2 D x6 xt (sI2 D) from (fs2_0 D x6 xt).symm, σ03_fs,
    if_neg (fun e => by have := congrArg Fin.val e; simp [sI2, sC2] at this), τOut3_I]

theorem σ03_tm : (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st (sTm D x6 xt) = sent (u.length + 1) := by
  rw [show sTm D x6 xt = fs2 D x6 xt (sT2 D) from Fin.ext (by rw [fs2_val]; simp [sT2, sTm]), σ03_fs,
    if_neg (fun e => by have := congrArg Fin.val e; simp [sT2, sC2] at this), τOut3_T]

theorem σ03_xs (j : ℕ) (hj : j < D) :
    (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st (xsN D x6 xt j) = sent ((u.length + 1 + c0) ^ (j + 1)) := by
  rw [← fs2_xs D x6 xt j (by omega), σ03_fs, if_neg (sxs2_ne D j (by omega)).2.2.2, τOut3_xs D c0 u j hj]

theorem σ03_xsD :
    (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st (xsN D x6 xt D) =
      List.replicate ((u.length + 1 + c0) ^ (D + 1) + 1) false := by
  rw [← fs2_xs D x6 xt D le_rfl, σ03_fs, if_neg (sxs2_ne D D le_rfl).2.2.2, τOut3_xsD]

theorem σ03_pad :
    (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st (sPad D x6 xt) = sent (u.length + 1 + c0) := by
  rw [show sPad D x6 xt = fs2 D x6 xt (sP2 D) from Fin.ext (by rw [fs2_val]; simp [sP2, sPad, sMisc]; omega), σ03_fs,
    if_neg (fun e => by have := congrArg Fin.val e; simp [sP2, sC2] at this), τOut3_P]

theorem σ03_blank (i : Fin (nsL D x6 xt + 1)) (h0 : i.val ≠ 0) (h9 : i.val ≠ 9) (hp : i.val ≠ 21 + D)
    (hx : i.val < 12 ∨ 12 + D < i.val) : (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).st i = [] := by
  by_cases h : ∃ k, fs2 D x6 xt k = i
  · obtain ⟨k, rfl⟩ := h
    rw [σ03_fs]
    have hv := fs2_val D x6 xt k
    have hk := k.isLt
    split_ifs with hc
    · rfl
    · exfalso
      apply hc
      apply Fin.ext
      rw [hv] at h0 h9 hp hx
      simp only [sC2]
      split_ifs at h0 h9 hp hx <;> omega
  · exact σ03_out D x6 xt c0 u i (fun k hk => h ⟨k, hk⟩)

theorem σ03_sh : ∀ i, (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).sh i = 0 := fun _ => rfl

theorem σ03_val : ∀ r, (σ03 (nr := nrL) D (fs2 D x6 xt) c0 u).val r = 0 := fun _ => rfl

end St3

end NearCubicWires.WireExponent3_5.FinalPass.S5T
