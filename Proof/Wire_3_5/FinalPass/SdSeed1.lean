import Proof.Wire_3_5.FinalPass.SdTab1

/-! # S4 (the seeds phase), part 17: the tables word's position kept in a register

During a seed's center loop every head must be at `0` (the center loop's static facts), so the tables word's head
goes back to `0` after the seed's tables are moved, its position saved in a register `rgP` (`203`): **`wmoveF_spec`**
(the register moved into another while a stream advances), **`wmoveB_spec`** (while it retreats), **`fwdP_spec`**
(`tTW` to the saved position), **`rewP_spec`** (back to `0`, the position saved), **`peek_spec`** (the flag `fS` (`202`)
set to the bit at the saved position: another seed's tables follow).

Paper quantity of the main type: none beyond the machine model (the seed loop's bookkeeping). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- Move register `a` into `b` while stream `X` advances. -/
def WmoveF (X : Fin (ns + 1)) (a b : Fin nr) : WM ns nr := .whr a (.seq (.dec a) (.seq (.fwd X) (.inc b)))

/-- Move register `a` into `b` while stream `X` retreats. -/
def WmoveB (X : Fin (ns + 1)) (a b : Fin nr) : WM ns nr := .whr a (.seq (.dec a) (.seq (.bwd X) (.inc b)))

theorem wmoveF_spec (X : Fin (ns + 1)) (a b : Fin nr) (hab : a ≠ b) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val a = n → σ.val a ≤ cap → σ.val b + σ.val a ≤ cap →
      WExec cap (WmoveF X a b) σ (((σ.setv a 0).setv b (σ.val b + n)).seth X (σ.sh X + n)) (9 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : ((σ.setv a 0).setv b (σ.val b + 0)).seth X (σ.sh X + 0) = σ := by
      rw [Nat.add_zero, Nat.add_zero, ← h0, wsetv_same, wsetv_same]
      exact WState.eq (by simp) rfl rfl rfl
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, ha, hb => by
    have h1 := WExec.dec (cap := cap) a σ ha
    have h2 := WExec.fwd (cap := cap) X (σ.setv a (σ.val a - 1))
    have hba : (σ.setv a (σ.val a - 1)).val b = σ.val b := wsetv_val_ne _ _ (Ne.symm hab)
    have h3 := WExec.inc (cap := cap) b ((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1))
      (by simp only [WState.seth_val]; rw [hba]; omega)
    have va : (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1)).setv b
        (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1)).val b + 1)).val a = σ.val a - 1 := by
      simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne hab, Function.update_self]
    have vb : (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1)).setv b
        (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1)).val b + 1)).val b = σ.val b + 1 := by
      simp only [WState.setv_val, WState.seth_val, Function.update_self]
      rw [Function.update_of_ne (Ne.symm hab)]
    have ih := wmoveF_spec X a b hab n (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1)).setv b
        (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X + 1)).val b + 1))
      (by rw [va]; omega) (by rw [va]; omega) (by rw [va, vb]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · funext j
      simp only [WState.seth_sh, WState.setv_sh]
      by_cases hj : j = X
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    · rfl
    · funext j
      simp only [WState.seth_val, WState.setv_val]
      by_cases hja : j = a
      · subst hja
        simp [Function.update_of_ne hab]
      · by_cases hjb : j = b
        · subst hjb
          simp [Function.update_of_ne hab, Function.update_of_ne (Ne.symm hab)]
          omega
        · simp [Function.update_of_ne hja, Function.update_of_ne hjb]
    · rfl

theorem wmoveB_spec (X : Fin (ns + 1)) (a b : Fin nr) (hab : a ≠ b) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val a = n → σ.val a ≤ cap → σ.val b + σ.val a ≤ cap →
      WExec cap (WmoveB X a b) σ (((σ.setv a 0).setv b (σ.val b + n)).seth X (σ.sh X - n)) (9 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : ((σ.setv a 0).setv b (σ.val b + 0)).seth X (σ.sh X - 0) = σ := by
      rw [Nat.add_zero, Nat.sub_zero, ← h0, wsetv_same, wsetv_same]
      exact WState.eq (by simp) rfl rfl rfl
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, ha, hb => by
    have h1 := WExec.dec (cap := cap) a σ ha
    have h2 := WExec.bwd (cap := cap) X (σ.setv a (σ.val a - 1))
    have hba : (σ.setv a (σ.val a - 1)).val b = σ.val b := wsetv_val_ne _ _ (Ne.symm hab)
    have h3 := WExec.inc (cap := cap) b ((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1))
      (by simp only [WState.seth_val]; rw [hba]; omega)
    have va : (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1)).setv b
        (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1)).val b + 1)).val a = σ.val a - 1 := by
      simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne hab, Function.update_self]
    have vb : (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1)).setv b
        (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1)).val b + 1)).val b = σ.val b + 1 := by
      simp only [WState.setv_val, WState.seth_val, Function.update_self]
      rw [Function.update_of_ne (Ne.symm hab)]
    have ih := wmoveB_spec X a b hab n (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1)).setv b
        (((σ.setv a (σ.val a - 1)).seth X ((σ.setv a (σ.val a - 1)).sh X - 1)).val b + 1))
      (by rw [va]; omega) (by rw [va]; omega) (by rw [va, vb]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · funext j
      simp only [WState.seth_sh, WState.setv_sh]
      by_cases hj : j = X
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]
    · rfl
    · funext j
      simp only [WState.seth_val, WState.setv_val]
      by_cases hja : j = a
      · subst hja
        simp [Function.update_of_ne hab]
      · by_cases hjb : j = b
        · subst hjb
          simp [Function.update_of_ne hab, Function.update_of_ne (Ne.symm hab)]
          omega
        · simp [Function.update_of_ne hja, Function.update_of_ne hjb]
    · rfl

end Gen

section Lay
variable {nw nn nsc nrs : ℕ}

/-- The seed flag and the tables word's saved position. -/
def fS : Fin (bnr nn nrs) := brg 202 (by omega)
def rgP : Fin (bnr nn nrs) := brg 203 (by omega)

theorem rgP_ne_T : (rgP : Fin (bnr nn nrs)) ≠ rgT := by simp only [rgP, rgT]; apply brg_ne; omega
theorem fS_ne_T : (fS : Fin (bnr nn nrs)) ≠ rgT := by simp only [fS, rgT]; apply brg_ne; omega
theorem fS_ne_P : (fS : Fin (bnr nn nrs)) ≠ rgP := by simp only [fS, rgP]; apply brg_ne; omega

/-- `tTW` to the saved position. -/
def fwdP : BP nw nn nsc nrs := WmoveF tTW rgP rgT
/-- `tTW` back to `0`, its position saved. -/
def rewP : BP nw nn nsc nrs := WmoveB tTW rgT rgP

theorem fwdP_spec (cap p : ℕ) (ω : BS nw nn nsc nrs) (hh : ω.sh tTW = 0) (hT : ω.val rgT = 0) (hP : ω.val rgP = p)
    (hc : p ≤ cap) : WExec cap fwdP ω (((ω.setv rgP 0).setv rgT p).seth tTW p) (9 * p + 1) := by
  have e := wmoveF_spec cap tTW rgP rgT rgP_ne_T p ω hP (by rw [hP]; exact hc) (by rw [hT, hP]; omega)
  simp only [hT, hh, Nat.zero_add] at e
  exact e

theorem rewP_spec (cap p : ℕ) (ω : BS nw nn nsc nrs) (hh : ω.sh tTW = p) (hT : ω.val rgT = p) (hP : ω.val rgP = 0)
    (hc : p ≤ cap) : WExec cap rewP ω (((ω.setv rgT 0).setv rgP p).seth tTW 0) (9 * p + 1) := by
  have e := wmoveB_spec cap tTW rgT rgP rgP_ne_T.symm p ω hT (by rw [hT]; exact hc) (by rw [hT, hP]; omega)
  simp only [hP, hh, Nat.zero_add, Nat.sub_self] at e
  exact e

/-- **The next seed's test**: the flag `fS` set to the bit at the saved position. -/
def peek : BP nw nn nsc nrs := .seq fwdP (.seq (.ifs tTW (.inc fS) .skip) rewP)

theorem peek_spec (cap p : ℕ) (ω : BS nw nn nsc nrs) (hh : ω.sh tTW = 0) (hT : ω.val rgT = 0) (hP : ω.val rgP = p)
    (hF : ω.val fS = 0) (hc : p + 1 ≤ cap) :
    WExec cap peek ω (ω.setv fS (readTapeBit (ω.st tTW) p).toNat) (9 * p + 1 + 1 + (4 + 1 + (9 * p + 1))) := by
  have e1 := fwdP_spec cap p ω hh hT hP (by omega)
  obtain ⟨ω1, h1⟩ : ∃ y, y = ((ω.setv rgP 0).setv rgT p).seth tTW p := ⟨_, rfl⟩
  rw [← h1] at e1
  have hb : wbit ω1 tTW = readTapeBit (ω.st tTW) p := by unfold wbit; rw [h1]; simp
  have hF1 : ω1.val fS = 0 := by
    rw [h1]; simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne fS_ne_T, Function.update_of_ne fS_ne_P, hF]
  obtain ⟨ω2, e2, h2⟩ : ∃ ω2, WExec cap (.ifs tTW (.inc fS) .skip) ω1 ω2 4 ∧
      ω2 = ω1.setv fS (readTapeBit (ω.st tTW) p).toNat := by
    cases hr : readTapeBit (ω.st tTW) p
    · refine ⟨ω1, WExec.mono (WExec.ifsF (by rw [hb, hr]) (WExec.skip _)) (by omega), ?_⟩
      rw [show (false).toNat = 0 from rfl, ← hF1, wsetv_same]
    · refine ⟨_, WExec.mono (WExec.ifsT (by rw [hb, hr]) (WExec.inc fS ω1 (by rw [hF1]; omega))) (by omega), ?_⟩
      rw [hF1]; rfl
  have hh2 : ω2.sh tTW = p := by rw [h2, h1]; simp
  have hT2 : ω2.val rgT = p := by
    rw [h2, h1]
    simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne fS_ne_T.symm, Function.update_self]
  have hP2 : ω2.val rgP = 0 := by
    rw [h2, h1]
    simp only [WState.setv_val, WState.seth_val]
    rw [Function.update_of_ne fS_ne_P.symm, Function.update_of_ne rgP_ne_T, Function.update_self]
  have e3 := rewP_spec cap p ω2 hh2 hT2 hP2 (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  rw [h2, h1]
  apply WState.eq
  · funext i
    simp only [WState.seth_sh, WState.setv_sh]
    by_cases hi : i = tTW
    · subst hi; simp [hh]
    · simp [Function.update_of_ne hi]
  · rfl
  · funext q
    simp only [WState.seth_val, WState.setv_val]
    by_cases hqP : q = rgP
    · subst hqP
      rw [Function.update_self, Function.update_of_ne fS_ne_P.symm, hP]
    · rw [Function.update_of_ne hqP]
      by_cases hqT : q = rgT
      · subst hqT
        rw [Function.update_self, Function.update_of_ne fS_ne_T.symm, hT]
      · rw [Function.update_of_ne hqT]
        by_cases hqF : q = fS
        · subst hqF
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hqF, Function.update_of_ne hqF, Function.update_of_ne hqT,
            Function.update_of_ne hqP]
  · rfl

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
