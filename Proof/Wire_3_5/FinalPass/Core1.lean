import Proof.Wire_3_5.FinalPass.S5TPost

/-! # S5Core, part 1: padding the register-length tapes to their exact length (P3:3170-3181)

The front's exit (`FrontOut`) leaves every register-length tape (off the words and the numbers) exactly
`0^{Kc·N^{Dc}+1}`. The core half pads them against a reference tape `T = 0 1^c` (head at `0`; the leading `0` stops the
way back): **`padP T j`** writes `0` on `j` at `0`, then, while `T` reads `1`, writes `0` on `j` and moves both heads
right, then moves both back while `T` reads `1`. From any content of length `≤ c + 1` the tape becomes `0^{c+1}`
(**`padP_exec`**, via `wr_zero`, **`padF_exec`**, **`padB_exec`**); **`padList T js`** / **`padList_exec`** pads a list
of tapes.

Paper quantity: none (the front's exact blank tapes, `FrontOut.blank`, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {t : ℕ}

/-- Move two heads the same way. -/
def moveTwo (T j : Fin t) (mv : HeadMove) : Fin t → HeadMove := fun i => if i = T ∨ i = j then mv else .stay

/-- The forward body: write `0` on the target, move both right. -/
def fwdB (T j : Fin t) : Prog t := .act (writeAt j false) (moveTwo T j .right)

/-- The backward body: move both left. -/
def bwdB (T j : Fin t) : Prog t := .act (fun _ => none) (moveTwo T j .left)

/-- **Pad `j` against `T`.** -/
def padP (T j : Fin t) : Prog t :=
  .seq (.act (writeAt j false) (fun _ => .stay)) (.seq (.act (fun _ => none) (moveTwo T j .right))
    (.seq (.loop T (fwdB T j)) (.seq (.act (fun _ => none) (moveTwo T j .left)) (.loop T (bwdB T j)))))

theorem wr_zero : ∀ (h : ℕ) (y : List Bool),
    writeTapeBit (List.replicate h false ++ y) h false = List.replicate (h + 1) false ++ y.drop 1
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | h + 1, y => by
    show false :: writeTapeBit (List.replicate h false ++ y) h false = _
    rw [wr_zero h y]; rfl

theorem readT_ref (c h : ℕ) : readTapeBit (false :: List.replicate c true) h = decide (1 ≤ h ∧ h ≤ c) := by
  unfold readTapeBit
  rcases h with _ | h
  · simp
  · simp only [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    by_cases hh : h < c
    · simp [hh] <;> omega
    · simp [hh] <;> omega

/-- **The forward pass.** -/
theorem padF_exec (T j : Fin t) (hTj : T ≠ j) (c : ℕ) (x : List Bool) :
    ∀ (m : ℕ) (b : Bank t), b.A T = false :: List.replicate c true → b.H T = b.H j → 1 ≤ b.H T →
      b.H T + m = c + 1 → b.A j = List.replicate (b.H j) false ++ x.drop (b.H j) →
      Exec (.loop T (fwdB T j)) b ⟨fun i => if i = T ∨ i = j then c + 1 else b.H i,
        Function.update b.A j (List.replicate (c + 1) false ++ x.drop (c + 1))⟩ (3 * m + 1)
  | 0, b, hT, hTj', _, hm, hA => by
    have hb : b.bit T = false := by unfold Bank.bit; rw [hT, readT_ref]; simp <;> omega
    have e : (⟨fun i => if i = T ∨ i = j then c + 1 else b.H i,
        Function.update b.A j (List.replicate (c + 1) false ++ x.drop (c + 1))⟩ : Bank t) = b := by
      apply Bank.ext'
      · intro i
        by_cases hi : i = T ∨ i = j
        · rcases hi with rfl | rfl <;> simp <;> omega
        · simp [hi]
      · intro i
        show Function.update b.A j (List.replicate (c + 1) false ++ x.drop (c + 1)) i = b.A i
        by_cases hi : i = j
        · subst hi; rw [Function.update_self, hA, show b.H i = c + 1 by omega]
        · rw [Function.update_of_ne hi]
    rw [e]; exact Exec.loopF hb
  | m + 1, b, hT, hTj', h1, hm, hA => by
    have hb : b.bit T = true := by unfold Bank.bit; rw [hT, readT_ref]; simp <;> omega
    have e1 := Exec.act b (writeAt j false) (moveTwo T j .right)
    obtain ⟨b1, hb1⟩ : ∃ d : Bank t, d = b.act (writeAt j false) (moveTwo T j .right) := ⟨_, rfl⟩
    rw [← hb1] at e1
    have hH1 : ∀ i, b1.H i = if i = T ∨ i = j then b.H i + 1 else b.H i := fun i => by
      rw [hb1]; simp only [Bank.act, moveTwo]; split_ifs <;> rfl
    have hA1 : b1.A = Function.update b.A j (List.replicate (b.H j + 1) false ++ x.drop (b.H j + 1)) := by
      rw [hb1]; funext i; simp only [Bank.act, writeAt]
      by_cases hi : i = j
      · subst hi; simp only [if_true, Function.update_self]; rw [hA, wr_zero, List.drop_drop]
      · simp [hi, Function.update_of_ne hi]
    have ih := padF_exec T j hTj c x m b1 (by rw [hA1, Function.update_of_ne hTj, hT])
      (by rw [hH1, hH1]; simp <;> omega) (by rw [hH1]; simp <;> omega) (by rw [hH1]; simp <;> omega)
      (by rw [hA1, Function.update_self, hH1]; simp)
    have e : (⟨fun i => if i = T ∨ i = j then c + 1 else b1.H i,
        Function.update b1.A j (List.replicate (c + 1) false ++ x.drop (c + 1))⟩ : Bank t) =
        ⟨fun i => if i = T ∨ i = j then c + 1 else b.H i,
        Function.update b.A j (List.replicate (c + 1) false ++ x.drop (c + 1))⟩ := by
      apply Bank.ext'
      · intro i
        by_cases hi : i = T ∨ i = j
        · simp [hi]
        · simp only [hi, if_false]; rw [hH1]; simp [hi]
      · intro i
        rw [hA1]
        by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_of_ne hi]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

/-- **The backward pass.** -/
theorem padB_exec (T j : Fin t) (c : ℕ) :
    ∀ (m : ℕ) (b : Bank t), b.A T = false :: List.replicate c true → b.H T = m → b.H j = m → m ≤ c →
      Exec (.loop T (bwdB T j)) b ⟨fun i => if i = T ∨ i = j then 0 else b.H i, b.A⟩ (3 * m + 1)
  | 0, b, hT, h1, h2, _ => by
    have hb : b.bit T = false := by unfold Bank.bit; rw [hT, readT_ref]; simp <;> omega
    have e : (⟨fun i => if i = T ∨ i = j then 0 else b.H i, b.A⟩ : Bank t) = b := by
      apply Bank.ext'
      · intro i
        by_cases hi : i = T ∨ i = j
        · rcases hi with rfl | rfl <;> simp <;> omega
        · simp [hi]
      · intro i; rfl
    rw [e]; exact Exec.loopF hb
  | m + 1, b, hT, h1, h2, hm => by
    have hb : b.bit T = true := by unfold Bank.bit; rw [hT, readT_ref]; simp <;> omega
    have e1 := Exec.act b (fun _ => none) (moveTwo T j .left)
    obtain ⟨b1, hb1⟩ : ∃ d : Bank t, d = b.act (fun _ => none) (moveTwo T j .left) := ⟨_, rfl⟩
    rw [← hb1] at e1
    have hH1 : ∀ i, b1.H i = if i = T ∨ i = j then b.H i - 1 else b.H i := fun i => by
      rw [hb1]; simp only [Bank.act, moveTwo]; split_ifs <;> rfl
    have hA1 : b1.A = b.A := by rw [hb1]; funext i; simp [Bank.act]
    have ih := padB_exec T j c m b1 (by rw [hA1, hT]) (by rw [hH1]; simp <;> omega) (by rw [hH1]; simp <;> omega)
      (by omega)
    have e : (⟨fun i => if i = T ∨ i = j then 0 else b1.H i, b1.A⟩ : Bank t) =
        ⟨fun i => if i = T ∨ i = j then 0 else b.H i, b.A⟩ := by
      apply Bank.ext'
      · intro i
        by_cases hi : i = T ∨ i = j
        · simp [hi]
        · simp only [hi, if_false]; rw [hH1]; simp [hi]
      · intro i; rw [hA1]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

/-- **A tape padded to `0^{c+1}`.** -/
theorem padP_exec (T j : Fin t) (hTj : T ≠ j) (c : ℕ) (b : Bank t) (hT : b.A T = false :: List.replicate c true)
    (hHT : b.H T = 0) (hHj : b.H j = 0) (hL : (b.A j).length ≤ c + 1) :
    Exec (padP T j) b ⟨b.H, Function.update b.A j (List.replicate (c + 1) false)⟩ (6 * c + 16) := by
  have e1 := Exec.act b (writeAt j false) (fun _ => .stay)
  obtain ⟨b1, hb1⟩ : ∃ d : Bank t, d = b.act (writeAt j false) (fun _ => .stay) := ⟨_, rfl⟩
  rw [← hb1] at e1
  have hH1 : b1.H = b.H := by rw [hb1]; funext i; rfl
  have hA1 : b1.A = Function.update b.A j (List.replicate 1 false ++ (b.A j).drop 1) := by
    rw [hb1]; funext i
    by_cases hi : i = j
    · subst hi
      show (match writeAt i false i with | none => b.A i | some v => writeTapeBit (b.A i) (b.H i) v) = _
      rw [Function.update_self, hHj]
      simp only [writeAt, if_true]
      have := wr_zero 0 (b.A i)
      rw [List.replicate_zero, List.nil_append] at this
      exact this
    · show (match writeAt j false i with | none => b.A i | some v => writeTapeBit (b.A i) (b.H i) v) = _
      simp [writeAt, hi, Function.update_of_ne hi]
  have e2 := Exec.act b1 (fun _ => none) (moveTwo T j .right)
  obtain ⟨b2, hb2⟩ : ∃ d : Bank t, d = b1.act (fun _ => none) (moveTwo T j .right) := ⟨_, rfl⟩
  rw [← hb2] at e2
  have hH2 : ∀ i, b2.H i = if i = T ∨ i = j then b.H i + 1 else b.H i := fun i => by
    rw [hb2, hH1.symm]; simp only [Bank.act, moveTwo]; split_ifs <;> rfl
  have hA2 : b2.A = b1.A := by rw [hb2]; funext i; simp [Bank.act]
  have e3 := padF_exec T j hTj c (b.A j) c b2 (by rw [hA2, hA1, Function.update_of_ne hTj, hT])
    (by rw [hH2, hH2]; simp [hHT, hHj]) (by rw [hH2]; simp <;> omega) (by rw [hH2]; simp <;> omega)
    (by rw [hA2, hA1, Function.update_self, hH2]; simp [hHj])
  obtain ⟨b3, hb3⟩ : ∃ d : Bank t, d = (⟨fun i => if i = T ∨ i = j then c + 1 else b2.H i,
      Function.update b2.A j (List.replicate (c + 1) false ++ (b.A j).drop (c + 1))⟩ : Bank t) := ⟨_, rfl⟩
  rw [← hb3] at e3
  have hdrop : (b.A j).drop (c + 1) = [] := List.drop_eq_nil_of_le hL
  have e4 := Exec.act b3 (fun _ => none) (moveTwo T j .left)
  obtain ⟨b4, hb4⟩ : ∃ d : Bank t, d = b3.act (fun _ => none) (moveTwo T j .left) := ⟨_, rfl⟩
  rw [← hb4] at e4
  have hH4 : ∀ i, b4.H i = if i = T ∨ i = j then c else b.H i := fun i => by
    rw [hb4]; simp only [Bank.act, moveTwo, hb3]
    by_cases hi : i = T ∨ i = j
    · simp [hi, HeadMove.apply]
    · simp only [hi, if_false]; rw [hH2]; simp [hi, HeadMove.apply]
  have hA4 : b4.A = Function.update b.A j (List.replicate (c + 1) false) := by
    rw [hb4]; funext i; simp only [Bank.act, hb3, hdrop, List.append_nil, hA2, hA1]
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have e5 := padB_exec T j c c b4 (by rw [hA4, Function.update_of_ne hTj, hT]) (by rw [hH4]; simp)
    (by rw [hH4]; simp) le_rfl
  have e : (⟨fun i => if i = T ∨ i = j then 0 else b4.H i, b4.A⟩ : Bank t) =
      ⟨b.H, Function.update b.A j (List.replicate (c + 1) false)⟩ := by
    apply Bank.ext'
    · intro i
      by_cases hi : i = T ∨ i = j
      · simp only [hi, if_true]; rcases hi with rfl | rfl <;> simp [hHT, hHj]
      · simp only [hi, if_false]; rw [hH4]; simp [hi]
    · intro i; rw [hA4]
  rw [e] at e5
  exact Exec.mono (Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq e4 e5)))) (by omega)

/-- Pad a list of tapes. -/
def padList (T : Fin t) : List (Fin t) → Prog t
  | [] => .skip
  | j :: js => .seq (padP T j) (padList T js)

/-- **A list of tapes padded to `0^{c+1}`**; heads and every other tape kept. -/
theorem padList_exec (T : Fin t) (c : ℕ) : ∀ (js : List (Fin t)) (b : Bank t), js.Nodup → T ∉ js →
    b.A T = false :: List.replicate c true → b.H T = 0 → (∀ j ∈ js, b.H j = 0 ∧ (b.A j).length ≤ c + 1) →
    Exec (padList T js) b ⟨b.H, fun i => if i ∈ js then List.replicate (c + 1) false else b.A i⟩
      (js.length * (6 * c + 17))
  | [], b, _, _, _, _, _ => by
    have e : (⟨b.H, fun i => if i ∈ ([] : List (Fin t)) then List.replicate (c + 1) false else b.A i⟩ :
        Bank t) = b := by
      apply Bank.ext'
      · intro i; rfl
      · intro i; simp
    rw [e]; exact Exec.mono (Exec.skip b) (by simp)
  | j :: js, b, hnd, hT, hA, hH, hj => by
    obtain ⟨hHj, hL⟩ := hj j List.mem_cons_self
    have hnj : j ∉ js := (List.nodup_cons.1 hnd).1
    have hTj : T ≠ j := fun e => hT (e ▸ List.mem_cons_self)
    have hTs : T ∉ js := fun h => hT (List.mem_cons_of_mem _ h)
    have e1 := padP_exec T j hTj c b hA hH hHj hL
    have ih := padList_exec T c js ⟨b.H, Function.update b.A j (List.replicate (c + 1) false)⟩
      (List.nodup_cons.1 hnd).2 hTs (by simp [Function.update_of_ne hTj, hA]) hH
      (fun j' hj' => by
        have hne : j' ≠ j := fun e => hnj (e ▸ hj')
        obtain ⟨h1, h2⟩ := hj j' (List.mem_cons_of_mem _ hj')
        exact ⟨h1, by simpa [Function.update_of_ne hne] using h2⟩)
    have e : (⟨b.H, fun i => if i ∈ js then List.replicate (c + 1) false
        else Function.update b.A j (List.replicate (c + 1) false) i⟩ : Bank t) =
        ⟨b.H, fun i => if i ∈ j :: js then List.replicate (c + 1) false else b.A i⟩ := by
      apply Bank.ext'
      · intro i; rfl
      · intro i
        by_cases hij : i = j
        · subst hij; simp [hnj]
        · by_cases hi : i ∈ js
          · simp [hi]
          · simp [hi, hij, Function.update_of_ne hij]
    rw [e] at ih
    refine Exec.mono (Exec.seq e1 ih) ?_
    rw [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.Core
