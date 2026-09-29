import Proof.Wire_3_5.FinalPass.S5TSt3

/-! # S5-THR, part 30: erasing register tapes after the scrub (P3:3170-3181)

A register tape of the word machine is `regTape cap v = 0 :: 1^v 0^{cap-v}` (a leading `0`). After the scrub its head
is at `0`; `eraseR` steps right over the leading `0`, then runs `eraseT`'s loops from cell `1`: the backward loop stops
on the leading `0`, the head back at `0`.

* `loopR1_exec`, `loopL1_exec`, `eraseR` / **`eraseR_exec`**; `eraseRegs` / **`eraseRegs_exec`**.

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

theorem loopR1_exec (j : Fin t) (v : ℕ) (rest : List Bool) (hr : rest.getD 0 false = false) :
    ∀ (m : ℕ) (b : Bank t), b.A j = false :: (List.replicate v true ++ rest) → b.H j + m = v + 1 → 1 ≤ b.H j →
      Exec (.loop j (.act (fun _ => none) (moveAt j .right))) b ⟨Function.update b.H j (v + 1), b.A⟩ (3 * m + 1)
  | 0, b, hA, hH, _ => by
    have hb : b.bit j = false := by
      unfold Bank.bit readTapeBit; rw [hA, show b.H j = v + 1 by omega, List.getD_cons_succ,
        List.getD_append_right _ _ _ _ (by simp)]
      simpa using hr
    have e : (⟨Function.update b.H j (v + 1), b.A⟩ : Bank t) = b := by
      rw [show v + 1 = b.H j by omega, Function.update_eq_self]
    rw [e]; exact Exec.loopF hb
  | m + 1, b, hA, hH, h1 => by
    have hb : b.bit j = true := by
      unfold Bank.bit readTapeBit
      obtain ⟨p, hp⟩ : ∃ p, b.H j = p + 1 := ⟨b.H j - 1, by omega⟩
      have hpv : p < v := by omega
      rw [hA, hp, List.getD_cons_succ, List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hpv]
    have e1 := Exec.act b (fun _ => none) (moveAt j .right)
    have ih := loopR1_exec j v rest hr m (b.act (fun _ => none) (moveAt j .right)) (by simp [Bank.act, hA])
      (by simp [Bank.act, moveAt, HeadMove.apply]; omega) (by simp [Bank.act, moveAt, HeadMove.apply])
    have e : (⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j (v + 1),
        (b.act (fun _ => none) (moveAt j .right)).A⟩ : Bank t) = ⟨Function.update b.H j (v + 1), b.A⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; simp [Bank.act]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

theorem loopL1_exec (j : Fin t) : ∀ (p q : ℕ) (b : Bank t),
    b.A j = false :: (List.replicate (p + 1) true ++ List.replicate q false) → b.H j = p + 1 →
      Exec (.loop j (.act (writeAt j false) (moveAt j .left))) b
        ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (p + 2 + q) false)⟩ (3 * (p + 1) + 1)
  | 0, q, b, hA, hH => by
    have hb : b.bit j = true := by unfold Bank.bit; rw [hA, hH]; rfl
    have e1 := Exec.act b (writeAt j false) (moveAt j .left)
    have hw : writeTapeBit (b.A j) (b.H j) false = List.replicate (0 + 2 + q) false := by
      have hm := writeTapeBit_mid [false] (List.replicate q false) true false
      simp only [List.length_singleton] at hm
      rw [hA, hH]
      show writeTapeBit ([false] ++ true :: List.replicate q false) 1 false = _
      rw [hm, show 0 + 2 + q = q + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]; rfl
    have e : b.act (writeAt j false) (moveAt j .left) =
        ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (0 + 2 + q) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp [Bank.act, moveAt, HeadMove.apply, hH]
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; by_cases hi : i = j
        · subst hi; simp only [Bank.act, writeAt, if_pos rfl, Function.update_self]; exact hw
        · simp [Function.update_apply, hi, Bank.act, writeAt]
    have hb2 : (b.act (writeAt j false) (moveAt j .left)).bit j = false := by
      rw [e]; unfold Bank.bit; simp [readTapeBit, List.replicate_succ]
    have e2 := Exec.loopF (P := .act (writeAt j false) (moveAt j .left)) hb2
    have e3 := Exec.loopT hb e1 e2
    rw [e] at e3
    exact Exec.mono e3 (by norm_num)
  | p + 1, q, b, hA, hH => by
    have hb : b.bit j = true := by
      unfold Bank.bit readTapeBit
      rw [hA, hH, List.getD_cons_succ, List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    have e1 := Exec.act b (writeAt j false) (moveAt j .left)
    have hw : writeTapeBit (b.A j) (b.H j) false =
        false :: (List.replicate (p + 1) true ++ List.replicate (q + 1) false) := by
      have hm := writeTapeBit_mid (false :: List.replicate (p + 1) true) (List.replicate q false) true false
      simp only [List.length_cons, List.length_replicate] at hm
      rw [hA, hH, show false :: (List.replicate (p + 1 + 1) true ++ List.replicate q false) =
        (false :: List.replicate (p + 1) true) ++ true :: List.replicate q false by
          rw [List.replicate_succ' (n := p + 1)]; simp only [List.cons_append, List.append_assoc, List.singleton_append,
            List.nil_append],
        hm]
      simp only [List.cons_append]; rfl
    have ih := loopL1_exec j p (q + 1) (b.act (writeAt j false) (moveAt j .left))
      (by simp only [Bank.act, writeAt, if_pos rfl]; exact hw)
      (by simp [Bank.act, moveAt, HeadMove.apply, hH])
    have e : (⟨Function.update (b.act (writeAt j false) (moveAt j .left)).H j 0,
        Function.update (b.act (writeAt j false) (moveAt j .left)).A j (List.replicate (p + 2 + (q + 1)) false)⟩ :
          Bank t) = ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (p + 1 + 2 + q) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; by_cases hi : i = j
        · subst hi; simp; omega
        · simp [Function.update_apply, hi, Bank.act, writeAt]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

/-- Erase a register tape `0 :: 1^v 0^k`: over the leading `0`, then `eraseT`'s loops. -/
def eraseR (j : Fin t) : Prog t := .seq (.act (fun _ => none) (moveAt j .right)) (eraseT j)

theorem eraseR_exec (j : Fin t) (b : Bank t) (v k : ℕ)
    (hA : b.A j = false :: (List.replicate v true ++ List.replicate k false)) (hH : b.H j = 0) :
    Exec (eraseR j) b ⟨b.H, Function.update b.A j (List.replicate (1 + v + k) false)⟩ (6 * v + 11) := by
  have e0 := Exec.act b (fun _ => none) (moveAt j .right)
  obtain ⟨b0, hb0⟩ : ∃ c : Bank t, c = b.act (fun _ => none) (moveAt j .right) := ⟨_, rfl⟩
  rw [← hb0] at e0
  have h0A : b0.A = b.A := by rw [hb0]; funext i; simp [Bank.act]
  have h0j : b0.H j = 1 := by rw [hb0]; simp [Bank.act, moveAt, HeadMove.apply, hH]
  have h0H : ∀ i, i ≠ j → b0.H i = b.H i := fun i hi => by rw [hb0]; simp [Bank.act, moveAt, hi, HeadMove.apply]
  have e1 := loopR1_exec j v (List.replicate k false) (by cases k <;> rfl) v b0 (by rw [h0A, hA]) (by omega) (by omega)
  obtain ⟨b1, hb1⟩ : ∃ c : Bank t, c = ⟨Function.update b0.H j (v + 1), b0.A⟩ := ⟨_, rfl⟩
  rw [← hb1] at e1
  have e2 := Exec.act b1 (fun _ => none) (moveAt j .left)
  obtain ⟨b2, hb2⟩ : ∃ c : Bank t, c = b1.act (fun _ => none) (moveAt j .left) := ⟨_, rfl⟩
  rw [← hb2] at e2
  have h2A : b2.A = b.A := by rw [hb2, hb1, h0A]; funext i; simp [Bank.act]
  have h2H : ∀ i, i ≠ j → b2.H i = b.H i := fun i hi => by
    rw [hb2, hb1]; simp [Bank.act, moveAt, hi, HeadMove.apply, h0H i hi]
  have h2j : b2.H j = v := by rw [hb2, hb1]; simp [Bank.act, moveAt, HeadMove.apply]
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv
    have hb : b2.bit j = false := by unfold Bank.bit; rw [h2A, hA, h2j]; rfl
    have e3 := Exec.loopF (P := .act (writeAt j false) (moveAt j .left)) hb
    have e : b2 = ⟨b.H, Function.update b.A j (List.replicate (1 + 0 + k) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; rw [h2j, hH]
        · exact h2H i hi
      · intro i; by_cases hi : i = j
        · subst hi; rw [h2A, hA]; simp [show 1 + 0 + k = k + 1 by omega, List.replicate_succ]
        · rw [h2A]; simp [Function.update_apply, hi]
    have e23 := Exec.seq e0 (Exec.seq e1 (Exec.seq e2 e3))
    rw [e] at e23
    exact Exec.mono e23 (by omega)
  · obtain ⟨p, rfl⟩ : ∃ p, v = p + 1 := ⟨v - 1, by omega⟩
    have e3 := loopL1_exec j p k b2 (by rw [h2A, hA]) h2j
    have e : (⟨Function.update b2.H j 0, Function.update b2.A j (List.replicate (p + 2 + k) false)⟩ : Bank t) =
        ⟨b.H, Function.update b.A j (List.replicate (1 + (p + 1) + k) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp [hH]
        · simp [Function.update_apply, hi, h2H i hi]
      · intro i; rw [h2A]; by_cases hi : i = j
        · subst hi; simp; omega
        · simp [Function.update_apply, hi]
    rw [e] at e3
    exact Exec.mono (Exec.seq e0 (Exec.seq e1 (Exec.seq e2 e3))) (by omega)

/-- Erase a list of register tapes. -/
def eraseRegs : List (Fin t) → Prog t
  | [] => .skip
  | j :: js => .seq (eraseR j) (eraseRegs js)

/-- **Register tapes erased**: each `0 :: 1^v 0^k` of length `≤ Lm` becomes zeros; heads and other tapes kept. -/
theorem eraseRegs_exec (Lm : ℕ) : ∀ (js : List (Fin t)) (b : Bank t), js.Nodup →
    (∀ j ∈ js, b.H j = 0 ∧ (∃ v k, b.A j = false :: (List.replicate v true ++ List.replicate k false)) ∧
      (b.A j).length ≤ Lm) →
    Exec (eraseRegs js) b ⟨b.H, fun i => if i ∈ js then List.replicate (b.A i).length false else b.A i⟩
      (js.length * (6 * Lm + 12))
  | [], b, _, _ => by
    have e : (⟨b.H, fun i => if i ∈ ([] : List (Fin t)) then List.replicate (b.A i).length false else b.A i⟩ :
        Bank t) = b := by
      apply Bank.ext'
      · intro i; rfl
      · intro i; simp
    rw [e]; exact Exec.mono (Exec.skip b) (by simp)
  | j :: js, b, hnd, hj => by
    obtain ⟨hH, ⟨v, k, hA⟩, hL⟩ := hj j List.mem_cons_self
    have hnj : j ∉ js := (List.nodup_cons.1 hnd).1
    have e1 := eraseR_exec j b v k hA hH
    have ih := eraseRegs_exec Lm js ⟨b.H, Function.update b.A j (List.replicate (1 + v + k) false)⟩
      (List.nodup_cons.1 hnd).2
      (fun j' hj' => by
        have hne : j' ≠ j := fun e => hnj (e ▸ hj')
        obtain ⟨h1, h2, h3⟩ := hj j' (List.mem_cons_of_mem _ hj')
        exact ⟨h1, by simpa [Function.update_of_ne hne] using h2, by simpa [Function.update_of_ne hne] using h3⟩)
    have hvk : 1 + v + k = (b.A j).length := by rw [hA]; simp; omega
    have e : (⟨b.H, fun i => if i ∈ js then List.replicate
        ((Function.update b.A j (List.replicate (1 + v + k) false)) i).length false
        else Function.update b.A j (List.replicate (1 + v + k) false) i⟩ : Bank t) =
        ⟨b.H, fun i => if i ∈ j :: js then List.replicate (b.A i).length false else b.A i⟩ := by
      apply Bank.ext'
      · intro i; rfl
      · intro i
        by_cases hij : i = j
        · subst hij; simp [hnj, hvk]
        · by_cases hi : i ∈ js
          · simp [hi, Function.update_of_ne hij]
          · simp [hi, hij, Function.update_of_ne hij]
    rw [e] at ih
    refine Exec.mono (Exec.seq e1 ih) ?_
    have : v ≤ Lm := by omega
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.S5T
