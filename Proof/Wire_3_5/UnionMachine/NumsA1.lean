import Proof.Wire_3_5.Primitive.Writers.DataSetup

/-! # NW phase (a), part 1: the unary kit (read a stashed number back, unframe the data word)

Phase (a) stashes the role registers as `1^v` on blank streams (PA's `SBWords.onesW`) around the SYM numbers program,
and moves the data stage's counts `dataWord cs = false :: frame (unaryList cs)` onto the numbers program's counts stream
as `unaryList cs`:

* `readU`, **`readU_spec`** (`1^v` on `O` ↦ `R := v`, the head back at `0`);
* `frame_mark`, `frame_pay` (the framed word's marker and payload cells), `ufBody`, `unframeW`, **`unframe_spec`**
  (`false :: frame u` on `O`, `C` blank ↦ `C := u`, both heads back at `0`).

Paper quantity: none (plumbing for the SYM call's counts). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- `R := |1^v|` from the stash `O` (counting the moves in `P`), the head back at `0`. -/
def readU (O : Fin (ns + 1)) (R P : Fin nr) : WM ns nr :=
  .seq (.whs O (.seq (.inc R) (.seq (.fwd O) (.inc P)))) (WM.rewind O P)

theorem readU_spec (O : Fin (ns + 1)) (R P : Fin nr) (hRP : R ≠ P) (v : ℕ) (σ : WState ns nr)
    (hO : σ.st O = List.replicate v true) (hh : σ.sh O = 0) (hR : σ.val R = 0) (hP : σ.val P = 0) (hv : v < cap) :
    WExec cap (readU O R P) σ (σ.setv R v) (16 * v + 3) := by
  let S : ℕ → WState ns nr := fun k => ((σ.seth O k).setv R k).setv P k
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext i; simp only [S, WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs with h
      · subst h; exact hh.symm
      · rfl
    · rfl
    · funext q; simp only [S, WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs with h1 h2
      · subst h1; exact hP.symm
      · subst h2; exact hR.symm
      · rfl
    · rfl
  have l1 := Data.whsLoop cap O (.seq (.inc R) (.seq (.fwd O) (.inc P))) 9 v S
    (fun k hk => by simp [S, wbit, hO, Data.rep_read, hk])
    (by simp [S, wbit, hO, Data.rep_read])
    (fun k hk => by
      have h1 := WExec.inc (cap := cap) R (S k) (by simp [S, hRP]; omega)
      have h2 := WExec.fwd (cap := cap) O ((S k).setv R ((S k).val R + 1))
      have h3 := WExec.inc (cap := cap) P (((S k).setv R ((S k).val R + 1)).seth O
        (((S k).setv R ((S k).val R + 1)).sh O + 1)) (by simp [S, Ne.symm hRP]; omega)
      refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
      simp only [S]
      wgen_eq [hRP, Ne.symm hRP])
  rw [hS0] at l1
  have h2 := wrewind_spec cap O P v (S v) (by simp [S]) (by simp [S]; omega)
  refine WExec.cast cap (WExec.seq l1 h2) ?_ (by omega)
  simp only [S]
  wgen_eq [hRP, Ne.symm hRP, hh, hP]

theorem frameP_mark : ∀ (u : List Bool) (k : ℕ),
    readTapeBit (frameP u ++ [false]) (2 * k) = decide (k < u.length)
  | [], 0 => rfl
  | [], k + 1 => by simp [readTapeBit, frameP]
  | b :: u, 0 => by simp [readTapeBit, frameP]
  | b :: u, k + 1 => by
    have ih := frameP_mark u k
    have e : frameP (b :: u) ++ [false] = true :: b :: (frameP u ++ [false]) := by simp [frameP]
    rw [e, show 2 * (k + 1) = 2 * k + 2 by ring]
    unfold readTapeBit at ih ⊢
    simp only [List.getD_cons_succ]
    rw [ih]
    simp

theorem frameP_pay : ∀ (u : List Bool) (k : ℕ) (hk : k < u.length),
    readTapeBit (frameP u ++ [false]) (2 * k + 1) = u[k]
  | [], _, hk => absurd hk (by simp)
  | b :: u, 0, _ => by simp [readTapeBit, frameP]
  | b :: u, k + 1, hk => by
    have ih := frameP_pay u k (by simp at hk; omega)
    have e : frameP (b :: u) ++ [false] = true :: b :: (frameP u ++ [false]) := by simp [frameP]
    rw [e, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring]
    unfold readTapeBit at ih ⊢
    simp only [List.getD_cons_succ]
    rw [ih]
    simp

theorem frame_mark (u : List Bool) (k : ℕ) :
    readTapeBit (false :: frame u) (1 + 2 * k) = decide (k < u.length) := by
  rw [frame_eq_frameP, ← frameP_mark u k, show 1 + 2 * k = 2 * k + 1 by ring]
  rfl

theorem frame_pay (u : List Bool) (k : ℕ) (hk : k < u.length) :
    readTapeBit (false :: frame u) (2 + 2 * k) = u[k] := by
  rw [frame_eq_frameP, ← frameP_pay u k hk, show 2 + 2 * k = 2 * k + 1 + 1 by ring]
  rfl

theorem write_take (u : List Bool) (k : ℕ) (hk : k < u.length) (b : Bool) (hb : u[k] = b) :
    writeTapeBit (u.take k) k b = u.take (k + 1) := by
  have e : ∀ l : List Bool, writeTapeBit l l.length b = l ++ [b] := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [writeTapeBit, ih]
  have hl : (u.take k).length = k := by simp; omega
  have := e (u.take k)
  rw [hl] at this
  rw [this, List.take_add_one, List.getElem?_eq_getElem hk, hb]
  rfl

/-- One round: past the marker, copy the payload bit onto `C`, past the payload. -/
def ufBody (O C : Fin (ns + 1)) (P Q : Fin nr) : WM ns nr :=
  .seq (.fwd O) (.seq (.inc P) (.seq (.ifs O (.wr C true) (.wr C false)) (.seq (.fwd C) (.seq (.inc Q)
    (.seq (.fwd O) (.inc P))))))

/-- **Unframe**: `false :: frame u` on `O` ↦ `u` on the blank `C`, both heads back at `0`. -/
def unframeW (O C : Fin (ns + 1)) (P Q : Fin nr) : WM ns nr :=
  .seq (.fwd O) (.seq (.inc P) (.seq (.whs O (ufBody O C P Q)) (.seq (WM.rewind O P) (WM.rewind C Q))))

theorem unframe_spec (O C : Fin (ns + 1)) (P Q : Fin nr) (hOC : O ≠ C) (hPQ : P ≠ Q) (u : List Bool)
    (σ : WState ns nr) (hO : σ.st O = false :: frame u) (hOh : σ.sh O = 0) (hC : σ.st C = []) (hCh : σ.sh C = 0)
    (hP : σ.val P = 0) (hQ : σ.val Q = 0) (hcap : 2 * u.length + 2 ≤ cap) :
    WExec cap (unframeW O C P Q) σ (σ.sets C u) (1 + 1 + (3 + 1 + ((u.length * (20 + 2) + 1) + 1 +
      ((5 * (1 + 2 * u.length) + 1) + 1 + (5 * u.length + 1))))) := by
  have hCO := Ne.symm hOC
  have hQP := Ne.symm hPQ
  have h1 := WExec.fwd (cap := cap) O σ
  have h2 := WExec.inc (cap := cap) P (σ.seth O (σ.sh O + 1)) (by simp [hP]; omega)
  let S : ℕ → WState ns nr := fun k =>
    ((((σ.sets C (u.take k)).seth C k).seth O (1 + 2 * k)).setv P (1 + 2 * k)).setv Q k
  have hS0 : S 0 = (σ.seth O (σ.sh O + 1)).setv P ((σ.seth O (σ.sh O + 1)).val P + 1) := by
    simp only [S]
    apply WState.eq
    · funext i; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs with h1' h2' <;> (try subst h1') <;> (try subst h2') <;> simp_all
    · funext i; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h1'
      · subst h1'; simp [hC]
      · rfl
    · funext q; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with h1' h2' <;> (try subst h1') <;> (try subst h2') <;> simp_all
    · rfl
  have sO : ∀ k, (S k).st O = false :: frame u := fun k => by simp [S, hOC, hO]
  have shO : ∀ k, (S k).sh O = 1 + 2 * k := fun k => by simp [S]
  have l1 := Data.whsLoop cap O (ufBody O C P Q) 20 u.length S
    (fun k hk => by simp only [wbit, sO, shO]; rw [frame_mark]; simp [hk])
    (by simp only [wbit, sO, shO]; rw [frame_mark]; simp)
    (fun k hk => by
      have hb := frame_pay u k hk
      have g1 := WExec.fwd (cap := cap) O (S k)
      obtain ⟨T1, hT1⟩ : ∃ s, s = (S k).seth O ((S k).sh O + 1) := ⟨_, rfl⟩
      rw [← hT1] at g1
      have g2 := WExec.inc (cap := cap) P T1 (by rw [hT1]; simp [S, hPQ]; omega)
      obtain ⟨T2, hT2⟩ : ∃ s, s = T1.setv P (T1.val P + 1) := ⟨_, rfl⟩
      rw [← hT2] at g2
      have wb : wbit T2 O = u[k] := by
        rw [hT2, hT1]; simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh,
          Function.update_self, sO, shO]
        rw [show 1 + 2 * k + 1 = 2 + 2 * k by ring]; exact hb
      have cst : T2.st C = u.take k := by rw [hT2, hT1]; simp [S]
      have csh : T2.sh C = k := by rw [hT2, hT1]; simp [S, hCO]
      obtain ⟨T3, g3, hT3⟩ : ∃ (s : WState ns nr), WExec cap (.ifs O (.wr C true) (.wr C false)) T2 s 2 ∧
          s = T2.sets C (u.take (k + 1)) := by
        cases hbk : u[k] with
        | true =>
          rw [hbk] at wb
          refine ⟨_, WExec.ifsT wb (WExec.wr C true T2), ?_⟩
          rw [cst, csh, write_take u k hk true hbk]
        | false =>
          rw [hbk] at wb
          refine ⟨_, WExec.ifsF wb (WExec.wr C false T2), ?_⟩
          rw [cst, csh, write_take u k hk false hbk]
      have g4 := WExec.fwd (cap := cap) C T3
      have g5 := WExec.inc (cap := cap) Q (T3.seth C (T3.sh C + 1)) (by rw [hT3, hT2, hT1]; simp [S, hQP]; omega)
      have g6 := WExec.fwd (cap := cap) O ((T3.seth C (T3.sh C + 1)).setv Q ((T3.seth C (T3.sh C + 1)).val Q + 1))
      have g7 := WExec.inc (cap := cap) P ((((T3.seth C (T3.sh C + 1)).setv Q
        ((T3.seth C (T3.sh C + 1)).val Q + 1))).seth O (((T3.seth C (T3.sh C + 1)).setv Q
        ((T3.seth C (T3.sh C + 1)).val Q + 1)).sh O + 1)) (by rw [hT3, hT2, hT1]; simp [S, hPQ, hQP]; omega)
      refine WExec.cast cap (WExec.seq g1 (WExec.seq g2 (WExec.seq g3 (WExec.seq g4 (WExec.seq g5
        (WExec.seq g6 g7)))))) ?_ (by omega)
      rw [hT3, hT2, hT1]
      simp only [S]
      apply WState.eq
      · funext i
        by_cases hiO : i = O
        · subst hiO; simp [hOC]; omega
        · by_cases hiC : i = C
          · subst hiC; simp [hCO]
          · simp [hiO, hiC]
      · funext i
        by_cases hiC : i = C
        · subst hiC; simp
        · simp [hiC]
      · funext q
        by_cases hqP : q = P
        · subst hqP; simp [hPQ]; omega
        · by_cases hqQ : q = Q
          · subst hqQ; simp [hQP]
          · simp [hqP, hqQ]
      · rfl)
  rw [← hS0] at h2
  have h3 := wrewind_spec cap O P (1 + 2 * u.length) (S u.length) (by simp [S, hPQ]) (by simp [S, hPQ]; omega)
  have h4 := wrewind_spec cap C Q u.length (((S u.length).setv P 0).seth O ((S u.length).sh O - (1 + 2 * u.length)))
    (by simp [S, hQP]) (by simp [S, hQP]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq l1 (WExec.seq h3 h4)))) ?_ le_rfl
  simp only [S]
  apply WState.eq
  · funext i
    by_cases hiO : i = O
    · subst hiO; simp [hOC, hOh]
    · by_cases hiC : i = C
      · subst hiC; simp [hCO, hCh]
      · simp [hiO, hiC]
  · funext i
    by_cases hiC : i = C
    · subst hiC; simp [List.take_length]
    · simp [hiC]
  · funext q
    by_cases hqP : q = P
    · subst hqP; simp [hPQ, hP]
    · by_cases hqQ : q = Q
      · subst hqQ; simp [hQ]
      · simp [hqP, hqQ]
  · rfl

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
