import Proof.Wire_3_5.FinalPass.S5TStageBase

/-! # S5-THR, part 28: erasing unary tapes after the scrub (P3:3170-3181)

After the scrub the THR half's register tapes hold `regTape cap v = 1^v 0^{cap+1-v}` and the scrub's driver holds
`1^W`, every head at `0`. The THR half must leave its scratch blank, and the scrub charges nothing here, so each such
tape is erased by a machine program (`Prog`): to the end of its ones, then backwards writing zeros; the head stops at
`0` (moving left at `0` stays, and the cell just written reads `0`).

* `eraseT` / **`eraseT_exec`** (one tape `1^v 0^k` → `0^{v+k}`, head back at `0`, every other tape and head kept);
* `eraseAll` / **`eraseAll_exec`** (a list of such tapes).

Paper quantity: none (the machine's clean exit, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {t : ℕ}

/-- Erase one unary tape: right over the ones, one step back, then zeros leftwards. -/
def eraseT (j : Fin t) : Prog t :=
  .seq (.loop j (.act (fun _ => none) (moveAt j .right)))
    (.seq (.act (fun _ => none) (moveAt j .left)) (.loop j (.act (writeAt j false) (moveAt j .left))))

theorem loopR_exec (j : Fin t) (v : ℕ) (rest : List Bool) (hr : rest.getD 0 false = false) :
    ∀ (m : ℕ) (b : Bank t), b.A j = List.replicate v true ++ rest → b.H j + m = v →
      Exec (.loop j (.act (fun _ => none) (moveAt j .right))) b ⟨Function.update b.H j v, b.A⟩ (3 * m + 1)
  | 0, b, hA, hH => by
    have hb : b.bit j = false := by
      unfold Bank.bit; rw [hA, show b.H j = v by omega]
      simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right] at hr ⊢; exact hr
    have e : (⟨Function.update b.H j v, b.A⟩ : Bank t) = b := by
      rw [show v = b.H j by omega, Function.update_eq_self]
    rw [e]; exact Exec.loopF hb
  | m + 1, b, hA, hH => by
    have hlt : b.H j < v := by omega
    have hb : b.bit j = true := by
      unfold Bank.bit readTapeBit; rw [hA, List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hlt]
    have e1 := Exec.act b (fun _ => none) (moveAt j .right)
    have ih := loopR_exec j v rest hr m (b.act (fun _ => none) (moveAt j .right)) (by simp [Bank.act, hA])
      (by simp [Bank.act, moveAt, HeadMove.apply]; omega)
    have e : (⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j v,
        (b.act (fun _ => none) (moveAt j .right)).A⟩ : Bank t) = ⟨Function.update b.H j v, b.A⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; simp [Bank.act]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

theorem loopL_exec (j : Fin t) : ∀ (p q : ℕ) (b : Bank t), b.A j = List.replicate (p + 1) true ++ List.replicate q false →
    b.H j = p → Exec (.loop j (.act (writeAt j false) (moveAt j .left))) b
      ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (p + 1 + q) false)⟩ (3 * (p + 1) + 1)
  | 0, q, b, hA, hH => by
    have hb : b.bit j = true := by unfold Bank.bit; rw [hA, hH]; rfl
    have e1 := Exec.act b (writeAt j false) (moveAt j .left)
    have hb2 : (b.act (writeAt j false) (moveAt j .left)).bit j = false := by
      unfold Bank.bit; simp [Bank.act, writeAt, moveAt, HeadMove.apply, hA, hH, writeTapeBit, readTapeBit]
    have e2 := Exec.loopF (P := .act (writeAt j false) (moveAt j .left)) hb2
    have e3 := Exec.loopT hb e1 e2
    have e : b.act (writeAt j false) (moveAt j .left) =
        ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (0 + 1 + q) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp [Bank.act, moveAt, HeadMove.apply, hH]
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; by_cases hi : i = j
        · subst hi
          have hm := writeTapeBit_mid [] (List.replicate q false) true false
          simp only [List.nil_append, List.length_nil] at hm
          simp only [Bank.act, writeAt, Function.update_self, hA, hH]
          show writeTapeBit (true :: List.replicate q false) 0 false = List.replicate (0 + 1 + q) false
          rw [hm, show 0 + 1 + q = q + 1 by omega, List.replicate_succ]
        · simp [Function.update_apply, hi, Bank.act, writeAt]
    rw [e] at e3
    exact Exec.mono e3 (by norm_num)
  | p + 1, q, b, hA, hH => by
    have hb : b.bit j = true := by
      unfold Bank.bit; rw [hA, hH]
      simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_replicate]
    have e1 := Exec.act b (writeAt j false) (moveAt j .left)
    have hw : writeTapeBit (b.A j) (b.H j) false = List.replicate (p + 1) true ++ List.replicate (q + 1) false := by
      have hm := writeTapeBit_mid (List.replicate (p + 1) true) (List.replicate q false) true false
      rw [List.length_replicate] at hm
      rw [hA, hH, show List.replicate (p + 1 + 1) true ++ List.replicate q false =
        List.replicate (p + 1) true ++ true :: List.replicate q false by
          rw [List.replicate_succ' (n := p + 1)]; simp only [List.append_assoc, List.singleton_append],
        hm]
      rfl
    have ih := loopL_exec j p (q + 1) (b.act (writeAt j false) (moveAt j .left))
      (by simp only [Bank.act, writeAt, if_pos rfl]; exact hw)
      (by simp [Bank.act, moveAt, HeadMove.apply, hH])
    have e : (⟨Function.update (b.act (writeAt j false) (moveAt j .left)).H j 0,
        Function.update (b.act (writeAt j false) (moveAt j .left)).A j (List.replicate (p + 1 + (q + 1)) false)⟩ :
          Bank t) = ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (p + 1 + 1 + q) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; by_cases hi : i = j
        · subst hi; simp; omega
        · simp [Function.update_apply, hi, Bank.act, writeAt]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

/-- **One unary tape erased**, its head back at `0`. -/
theorem eraseT_exec (j : Fin t) (b : Bank t) (v k : ℕ) (hA : b.A j = List.replicate v true ++ List.replicate k false)
    (hH : b.H j = 0) :
    Exec (eraseT j) b ⟨b.H, Function.update b.A j (List.replicate (v + k) false)⟩ (6 * v + 8) := by
  have e1 := loopR_exec j v (List.replicate k false) (by cases k <;> rfl) v b hA (by omega)
  obtain ⟨b1, hb1⟩ : ∃ c : Bank t, c = ⟨Function.update b.H j v, b.A⟩ := ⟨_, rfl⟩
  rw [← hb1] at e1
  have e2 := Exec.act b1 (fun _ => none) (moveAt j .left)
  obtain ⟨b2, hb2⟩ : ∃ c : Bank t, c = b1.act (fun _ => none) (moveAt j .left) := ⟨_, rfl⟩
  rw [← hb2] at e2
  have h2A : b2.A = b.A := by rw [hb2, hb1]; funext i; simp [Bank.act]
  have h2H : ∀ i, i ≠ j → b2.H i = b.H i := fun i hi => by
    rw [hb2, hb1]; simp [Bank.act, moveAt, hi, HeadMove.apply]
  have h2j : b2.H j = v - 1 := by rw [hb2, hb1]; simp [Bank.act, moveAt, HeadMove.apply]
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv
    have hb : b2.bit j = false := by
      unfold Bank.bit; rw [h2A, hA, h2j]; cases k <;> rfl
    have e3 := Exec.loopF (P := .act (writeAt j false) (moveAt j .left)) hb
    have e : b2 = ⟨b.H, Function.update b.A j (List.replicate (0 + k) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; rw [h2j, hH]
        · exact h2H i hi
      · intro i; by_cases hi : i = j
        · subst hi; rw [h2A, hA]; simp
        · rw [h2A]; simp [Function.update_apply, hi]
    have e23 := Exec.seq e1 (Exec.seq e2 e3)
    rw [e] at e23
    exact Exec.mono e23 (by omega)
  · obtain ⟨p, rfl⟩ : ∃ p, v = p + 1 := ⟨v - 1, by omega⟩
    have e3 := loopL_exec j p k b2 (by rw [h2A, hA]) (by rw [h2j]; omega)
    have e : (⟨Function.update b2.H j 0, Function.update b2.A j (List.replicate (p + 1 + k) false)⟩ : Bank t) =
        ⟨b.H, Function.update b.A j (List.replicate (p + 1 + k) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp [hH]
        · simp [Function.update_apply, hi, h2H i hi]
      · intro i; rw [h2A]
    rw [e] at e3
    exact Exec.mono (Exec.seq e1 (Exec.seq e2 e3)) (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.S5T
