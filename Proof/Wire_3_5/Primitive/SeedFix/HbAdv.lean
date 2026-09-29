import Proof.Wire_3_5.Primitive.SeedFix.HbCellT

/-! # C4.Hb, machine part 11: the odometer's step (`filt:soft`, P3:2253-2290)

The machine enumerates the cells of `hashTermsM` ("Expand each `A`-product into at most `2^{2t}` signed products",
P3:2262-2263) with an odometer: the binary word `CTR` (the sign pattern, then the positions; low bit first) is
incremented, and its carry steps the unary counters of the level `λ ≤ J`, the population, the aux seed and the star
row, each against its ruler; the row counter's carry clears the loop's bit `MORE`.

Paper quantity of the main type (**`advW_spec`**): the next cell of the enumeration (`binSucc`, `odoStep`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (write_boundary)

/-- The ruler of the odometer's binary word. -/
scoped notation "sCR" => (22 : Fin 24)

section Bin
variable (cap : ℕ)

/-- The number of leading ones. -/
def lead : List Bool → ℕ
  | true :: w => lead w + 1
  | _ => 0

theorem lead_le : ∀ w : List Bool, lead w ≤ w.length
  | [] => le_refl _
  | true :: w => by have := lead_le w; simp only [lead, List.length_cons]; omega
  | false :: w => by simp [lead]

theorem drop_lead : ∀ w : List Bool, lead w < w.length → w.drop (lead w) = false :: w.drop (lead w + 1)
  | [], h => by simp [lead] at h
  | true :: w, h => by
    simp only [lead, List.length_cons] at h ⊢
    simp only [List.drop_succ_cons]
    exact drop_lead w (by omega)
  | false :: w, _ => by simp [lead]

/-- **The binary successor** (low bit first), wrapping to zero. -/
def binSucc (w : List Bool) : List Bool :=
  if lead w < w.length then List.replicate (lead w) false ++ true :: w.drop (lead w + 1)
  else List.replicate w.length false

theorem write_mid (pre rest : List Bool) (b x : Bool) :
    writeTapeBit (pre ++ b :: rest) pre.length x = pre ++ x :: rest := by
  rw [write_boundary]; rfl

def binLoopW : HW := .whs sCTR (.seq (.wr sCTR false) (.seq (.fwd sCTR) (.fwd sCR)))

theorem binLoop_spec : ∀ (w : List Bool) (k : ℕ) (σ : HS), σ.st sCTR = List.replicate k false ++ w →
    σ.sh sCTR = k → σ.sh sCR = k →
    WExec cap binLoopW σ (((σ.sets sCTR (List.replicate (k + lead w) false ++ w.drop (lead w))).seth sCTR
      (k + lead w)).seth sCR (k + lead w)) (7 * lead w + 1)
  | [], k, σ, hC, hh, hr => by
    have hb : wbit σ sCTR = false := by simp [wbit, hC, hh, readTapeBit]
    refine WExec.cast cap (WExec.whsF hb) ?_ (by simp [lead])
    simp only [lead, Nat.add_zero, List.drop_nil]
    rw [← hC, ← hh]
    wst
    all_goals (try simp_all)
  | false :: w, k, σ, hC, hh, hr => by
    have hb : wbit σ sCTR = false := by
      simp only [wbit, hC, hh, readTapeBit]
      rw [List.getD_append_right _ _ _ _ (by simp)]; simp
    refine WExec.cast cap (WExec.whsF hb) ?_ (by simp [lead])
    simp only [lead, Nat.add_zero, List.drop_zero]
    rw [← hC, ← hh]
    wst
    all_goals (try simp_all)
  | true :: w, k, σ, hC, hh, hr => by
    have hb : wbit σ sCTR = true := by
      simp only [wbit, hC, hh, readTapeBit]
      rw [List.getD_append_right _ _ _ _ (by simp)]; simp
    have s1 := WExec.wr (cap := cap) sCTR false σ
    set σ1 := σ.sets sCTR (writeTapeBit (σ.st sCTR) (σ.sh sCTR) false) with hσ1
    have e1 : σ1.st sCTR = List.replicate (k + 1) false ++ w := by
      simp only [σ1, WState.sets_st, Function.update_self, hC, hh]
      have := write_mid (List.replicate k false) w true false
      rw [List.length_replicate] at this
      rw [this, List.replicate_succ', List.append_assoc]; rfl
    have s2 := WExec.fwd (cap := cap) sCTR σ1
    have s3 := WExec.fwd (cap := cap) sCR (σ1.seth sCTR (σ1.sh sCTR + 1))
    have ih := binLoop_spec w (k + 1) ((σ1.seth sCTR (σ1.sh sCTR + 1)).seth sCR
      ((σ1.seth sCTR (σ1.sh sCTR + 1)).sh sCR + 1)) (by simpa using e1)
      (by simp [σ1, hh]) (by simp [σ1, hr])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ (by simp only [lead]; omega)
    simp only [lead, List.drop_succ_cons]
    have ek : k + 1 + lead w = k + (lead w + 1) := by omega
    rw [ek]
    wst
    all_goals (try simp_all)

/-- **The binary increment** of `CTR` against its ruler `CR`; the carry out in register `24`. -/
def binIncW : HW := .seq (.inc 24) (.seq binLoopW (.ifs sCR (.seq (.wr sCTR true) (.dec 24)) .skip))

theorem binIncW_spec (w : List Bool) (σ : HS) (hC : σ.st sCTR = w) (hR : σ.st sCR = List.replicate w.length true)
    (hCh : σ.sh sCTR = 0) (hRh : σ.sh sCR = 0) (h24 : σ.val 24 = 0) (hcap : 1 ≤ cap) :
    ∃ τ, WExec cap binIncW σ τ (7 * w.length + 12) ∧ τ.st = Function.update σ.st sCTR (binSucc w) ∧
      τ.val = Function.update σ.val 24 (if lead w < w.length then 0 else 1) ∧ τ.cell = σ.cell ∧
      ∀ i, i ≠ sCTR → i ≠ sCR → τ.sh i = σ.sh i := by
  have hl := lead_le w
  have s1 := WExec.inc (cap := cap) 24 σ (by omega)
  set σ1 := σ.setv 24 (σ.val 24 + 1) with hσ1
  have s2 := binLoop_spec cap w 0 σ1 (by simp [σ1, hC]) (by simp [σ1, hCh]) (by simp [σ1, hRh])
  simp only [Nat.zero_add] at s2
  set σ2 := ((σ1.sets sCTR (List.replicate (lead w) false ++ w.drop (lead w))).seth sCTR (lead w)).seth sCR (lead w)
    with hσ2
  by_cases hlt : lead w < w.length
  · have hb : wbit σ2 sCR = true := by
      simp [wbit, σ2, σ1, hR, readTapeBit, hlt]
    have s3 := WExec.wr (cap := cap) sCTR true σ2
    set σ3 := σ2.sets sCTR (writeTapeBit (σ2.st sCTR) (σ2.sh sCTR) true) with hσ3
    have s4 := WExec.dec (cap := cap) 24 σ3 (by simp [σ3, σ2, σ1, h24]; omega)
    refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.ifsT (Q := WM.skip) hb (WExec.seq s3 s4))))
      (by omega), ?_, ?_, ?_, ?_⟩
    · have hs2 : σ2.st sCTR = List.replicate (lead w) false ++ w.drop (lead w) := by simp [σ2, σ1]
      have hh2 : σ2.sh sCTR = lead w := by simp [σ2, σ1]
      have e3 : σ3.st sCTR = binSucc w := by
        simp only [σ3, WState.sets_st, Function.update_self]
        rw [hs2, hh2, drop_lead w hlt]
        have := write_mid (List.replicate (lead w) false) (w.drop (lead w + 1)) false true
        rw [List.length_replicate] at this
        rw [this]; simp [binSucc, hlt]
      funext i
      by_cases h : i = sCTR
      · subst h; simp only [WState.setv_st, Function.update_self]; exact e3
      · simp [σ3, σ2, σ1, Function.update_of_ne h]
    · funext r; simp only [σ3, σ2, σ1, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · intro i h1 h2; simp [σ3, σ2, σ1, Function.update_of_ne h1, Function.update_of_ne h2]
  · have heq : lead w = w.length := by omega
    have hb : wbit σ2 sCR = false := by
      simp [wbit, σ2, σ1, hR, readTapeBit, heq]
    refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.ifsF (P := WM.seq (WM.wr sCTR true) (WM.dec 24)) hb
      (WExec.skip _)))) (by omega), ?_, ?_, ?_, ?_⟩
    · funext i
      by_cases h : i = sCTR
      · subst h; simp [σ2, σ1, binSucc, hlt, heq]
      · simp [σ2, σ1, Function.update_of_ne h]
    · funext r; simp only [σ2, σ1, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · intro i h1 h2; simp [σ2, σ1, Function.update_of_ne h1, Function.update_of_ne h2]

end Bin

section Unary
variable (cap : ℕ)

/-- Walk the ones of a unary counter `C`, its ruler `R` alongside. -/
def walkW (C R : Fin 24) : HW := .whs C (.seq (.fwd C) (.fwd R))

theorem walk_spec (C R : Fin 24) (hCR : C ≠ R) (n : ℕ) (rest : List Bool) (hr : rest.getD 0 false = false) :
    ∀ (k : ℕ) (σ : HS), k ≤ n → σ.st C = List.replicate n true ++ rest → σ.sh C = k → σ.sh R = k →
      WExec cap (walkW C R) σ ((σ.seth C n).seth R n) (5 * (n - k) + 1)
  | k, σ, hk, hC, hCh, hRh => by
    by_cases hkn : k = n
    · subst hkn
      have hb : wbit σ C = false := by
        simp only [wbit, hC, hCh, readTapeBit]
        rw [List.getD_append_right _ _ _ _ (by simp)]; simpa using hr
      refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
      wst
      all_goals (try simp_all)
    · have hlt : k < n := by omega
      have hb : wbit σ C = true := by
        simp only [wbit, hC, hCh, readTapeBit]
        rw [List.getD_append _ _ _ _ (by simp; omega)]; simp [hlt]
      have s1 := WExec.fwd (cap := cap) C σ
      have s2 := WExec.fwd (cap := cap) R (σ.seth C (σ.sh C + 1))
      have ih := walk_spec C R hCR n rest hr (k + 1) ((σ.seth C (σ.sh C + 1)).seth R
        ((σ.seth C (σ.sh C + 1)).sh R + 1)) (by omega) (by simpa using hC)
        (by simp [Function.update_of_ne hCR, hCh])
        (by simp [Function.update_of_ne (Ne.symm hCR), hRh])
      refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 s2) ih) ?_ (by omega)
      wst
      all_goals (try simp_all)
  termination_by k => n - k

/-- Clear a unary counter of ones from its last one back to cell `0`. -/
def zeroLoopW (C : Fin 24) : HW := .whs C (.seq (.wr C false) (.bwd C))

theorem zeroLoop_spec (C : Fin 24) : ∀ (j r : ℕ) (σ : HS), σ.st C = List.replicate (j + 1) true ++
    List.replicate r false → σ.sh C = j →
    WExec cap (zeroLoopW C) σ ((σ.sets C (List.replicate (j + 1 + r) false)).seth C 0) (5 * (j + 1) + 1)
  | 0, r, σ, hC, hh => by
    have hb : wbit σ C = true := by simp [wbit, hC, hh, readTapeBit]
    have s1 := WExec.wr (cap := cap) C false σ
    set σ1 := σ.sets C (writeTapeBit (σ.st C) (σ.sh C) false) with hσ1
    have e1 : σ1.st C = List.replicate (1 + r) false := by
      simp only [σ1, WState.sets_st, Function.update_self, hC, hh]
      rw [show 1 + r = r + 1 by omega]; rfl
    have s2 := WExec.bwd (cap := cap) C σ1
    have hb2 : wbit (σ1.seth C (σ1.sh C - 1)) C = false := by
      simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, e1, readTapeBit]
      simp
    refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 s2) (WExec.whsF hb2)) ?_ (by omega)
    wst
    all_goals (try simp_all)
  | j + 1, r, σ, hC, hh => by
    have hb : wbit σ C = true := by
      simp only [wbit, hC, hh, readTapeBit]
      rw [List.getD_append _ _ _ _ (by simp)]; simp
    have s1 := WExec.wr (cap := cap) C false σ
    set σ1 := σ.sets C (writeTapeBit (σ.st C) (σ.sh C) false) with hσ1
    have e1 : σ1.st C = List.replicate (j + 1) true ++ List.replicate (r + 1) false := by
      simp only [σ1, WState.sets_st, Function.update_self, hC, hh]
      have h1 : List.replicate (j + 1 + 1) true ++ List.replicate r false =
          List.replicate (j + 1) true ++ true :: List.replicate r false := by
        rw [List.replicate_succ', List.append_assoc]; rfl
      rw [h1]
      have := write_mid (List.replicate (j + 1) true) (List.replicate r false) true false
      rw [List.length_replicate] at this
      rw [this]; rfl
    have s2 := WExec.bwd (cap := cap) C σ1
    have ih := zeroLoop_spec C j (r + 1) (σ1.seth C (σ1.sh C - 1)) (by simpa using e1) (by simp [σ1, hh])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 s2) ih) ?_ (by omega)
    have ek : j + 1 + (r + 1) = j + 1 + 1 + r := by omega
    rw [ek]
    wst
    all_goals (try simp_all)

/-- **One unary counter step** (carry set in register `24`): the next value, or back to `0` with the carry kept. -/
def incUW (C R : Fin 24) : HW :=
  .seq (walkW C R) (.ifs R (.seq (.wr C true) (.dec 24)) (.seq (.bwd C) (zeroLoopW C)))

theorem incU_spec (C R : Fin 24) (hCR : C ≠ R) (v R' : ℕ) (hv : v < R') (σ : HS) (hC : σ.st C = unary v R')
    (hR : σ.st R = List.replicate (R' - 1) true) (hCh : σ.sh C = 0) (hRh : σ.sh R = 0) (h24 : σ.val 24 = 1)
    (hcap : 1 ≤ cap) :
    ∃ τ n, n ≤ 15 * R' + 10 ∧ WExec cap (incUW C R) σ τ n ∧
      τ.st = Function.update σ.st C (unary (if v + 1 < R' then v + 1 else 0) R') ∧
      τ.val = Function.update σ.val 24 (if v + 1 < R' then 0 else 1) ∧ τ.cell = σ.cell ∧
      ∀ i, i ≠ C → i ≠ R → τ.sh i = σ.sh i := by
  have gz : ∀ n : ℕ, (List.replicate n false).getD 0 false = false := fun n => by cases n <;> rfl
  have s1 := walk_spec cap C R hCR v (List.replicate (R' - 1 - v) false) (gz _) 0 σ (Nat.zero_le _) hC hCh hRh
  set σ1 := (σ.seth C v).seth R v with hσ1
  have h1R : σ1.sh R = v := by simp [σ1]
  have h1C : σ1.sh C = v := by simp [σ1, Function.update_of_ne hCR]
  have s1R : σ1.st R = List.replicate (R' - 1) true := by simp [σ1, hR]
  have s1C : σ1.st C = unary v R' := by simp [σ1, hC]
  have v24 : σ1.val 24 = 1 := by simp [σ1, h24]
  by_cases hlt : v + 1 < R'
  · have hb : wbit σ1 R = true := by
      show readTapeBit (σ1.st R) (σ1.sh R) = true
      rw [s1R, h1R]
      unfold readTapeBit
      rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega)]
      simp
    have s2 := WExec.wr (cap := cap) C true σ1
    set σ2 := σ1.sets C (writeTapeBit (σ1.st C) (σ1.sh C) true) with hσ2
    have e2 : σ2.st C = unary (v + 1) R' := by
      simp only [σ2, WState.sets_st, Function.update_self]
      rw [s1C, h1C]
      unfold unary
      have er : R' - 1 - v = (R' - 1 - (v + 1)) + 1 := by omega
      rw [er, List.replicate_succ]
      have := write_mid (List.replicate v true) (List.replicate (R' - 1 - (v + 1)) false) false true
      rw [List.length_replicate] at this
      rw [this, List.replicate_succ', List.append_assoc]; rfl
    have v2 : σ2.val 24 = 1 := by simp [σ2, v24]
    have s3 := WExec.dec (cap := cap) 24 σ2 (by rw [v2]; omega)
    refine ⟨_, _, ?_, WExec.seq s1 (WExec.ifsT (Q := WM.seq (WM.bwd C) (zeroLoopW C)) hb (WExec.seq s2 s3)),
      ?_, ?_, ?_, ?_⟩
    · omega
    · funext i
      by_cases h : i = C
      · subst h; simp only [WState.setv_st, Function.update_self, if_pos hlt]; exact e2
      · simp [σ2, σ1, Function.update_of_ne h]
    · funext r; simp only [σ2, σ1, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply, if_pos hlt]
      split_ifs <;> simp_all
    · rfl
    · intro i h1 h2; simp [σ2, σ1, Function.update_of_ne h1, Function.update_of_ne h2]
  · have heq : v + 1 = R' := by omega
    have hb : wbit σ1 R = false := by
      show readTapeBit (σ1.st R) (σ1.sh R) = false
      rw [s1R, h1R]
      unfold readTapeBit
      rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]
    have hC1 : σ1.st C = List.replicate v true := by
      rw [s1C]; unfold unary
      have : R' - 1 - v = 0 := by omega
      rw [this]; simp
    have s2 := WExec.bwd (cap := cap) C σ1
    set σ2 := σ1.seth C (σ1.sh C - 1) with hσ2
    have hfin : ∃ n3, n3 ≤ 5 * v + 1 ∧ WExec cap (zeroLoopW C) σ2 ((σ2.sets C (List.replicate v false)).seth C 0) n3 := by
      cases v with
      | zero =>
        have hb0 : wbit σ2 C = false := by
          simp [wbit, σ2, hC1, readTapeBit]
        refine ⟨1, le_refl _, WExec.cast cap (WExec.whsF hb0) ?_ (le_refl _)⟩
        simp only [List.replicate_zero]
        wst
        all_goals (try simp_all)
      | succ j =>
        have hz := zeroLoop_spec cap C j 0 σ2 (by simp [σ2, hC1]) (by simp [σ2, h1C])
        refine ⟨_, by omega, WExec.cast cap hz ?_ (le_refl _)⟩
        simp
    obtain ⟨n3, hn3, s3⟩ := hfin
    refine ⟨_, _, ?_, WExec.seq s1 (WExec.ifsF (P := WM.seq (WM.wr C true) (WM.dec 24)) hb (WExec.seq s2 s3)),
      ?_, ?_, ?_, ?_⟩
    · omega
    · funext i
      by_cases h : i = C
      · subst h; simp [σ2, σ1, if_neg hlt, unary, heq.symm]
      · simp [σ2, σ1, Function.update_of_ne h]
    · funext r; simp only [σ2, σ1, WState.seth_val, WState.sets_val, Function.update_apply, if_neg hlt]
      split_ifs <;> simp_all
    · rfl
    · intro i h1 h2; simp [σ2, σ1, Function.update_of_ne h1, Function.update_of_ne h2]

end Unary

section Adv
variable (cap : ℕ)

/-- One digit of the odometer: the value `v < R` and the incoming carry `c ≤ 1`. -/
def dstep (c v R : ℕ) : ℕ × ℕ := if c = 0 then (v, 0) else if v + 1 < R then (v + 1, 0) else (0, 1)

theorem dstep_carry_le (c v R : ℕ) : (dstep c v R).2 ≤ 1 := by
  unfold dstep; split_ifs <;> simp

theorem stepU_spec (C R : Fin 24) (hCR : C ≠ R) (v R' c : ℕ) (hc : c ≤ 1) (hv : v < R') (σ : HS)
    (hC : σ.st C = unary v R') (hR : σ.st R = List.replicate (R' - 1) true) (hCh : σ.sh C = 0) (hRh : σ.sh R = 0)
    (h24 : σ.val 24 = c) (hcap : 1 ≤ cap) :
    ∃ τ n, n ≤ 15 * R' + 11 ∧ WExec cap (.ifr 24 (incUW C R) .skip) σ τ n ∧
      τ.st = Function.update σ.st C (unary (dstep c v R').1 R') ∧
      τ.val = Function.update σ.val 24 (dstep c v R').2 ∧ τ.cell = σ.cell ∧
      ∀ i, i ≠ C → i ≠ R → τ.sh i = σ.sh i := by
  by_cases h0 : c = 0
  · subst h0
    refine ⟨σ, 1, by omega, WExec.ifrF (P := incUW C R) h24 (WExec.skip σ), ?_, ?_, rfl, fun _ _ _ => rfl⟩
    · exact (Function.update_eq_self_iff.mpr hC.symm).symm
    · exact (Function.update_eq_self_iff.mpr h24.symm).symm
  · have h1 : c = 1 := by omega
    subst h1
    obtain ⟨τ, n, hn, s, hst, hval, hcell, hsh⟩ := incU_spec cap C R hCR v R' hv σ hC hR hCh hRh h24 hcap
    refine ⟨τ, n + 1, by omega, WExec.ifrT (Q := WM.skip) (by rw [h24]; decide) s, ?_, ?_, hcell, hsh⟩
    · rw [hst]; unfold dstep; split_ifs <;> simp_all
    · rw [hval]; unfold dstep; split_ifs <;> simp_all

/-- The odometer's counters: the level, the population, the aux seed, the row, and the carry out. -/
structure Odo where
  lam : ℕ
  p : ℕ
  e : ℕ
  q : ℕ
  c : ℕ

/-- **The odometer's step** after the binary word's carry `c₀`. -/
def odoStep (J P nE N2 c0 : ℕ) (o : Odo) : Odo :=
  ⟨(dstep c0 o.lam (J + 1)).1, (dstep (dstep c0 o.lam (J + 1)).2 o.p P).1,
    (dstep (dstep (dstep c0 o.lam (J + 1)).2 o.p P).2 o.e nE).1,
    (dstep (dstep (dstep (dstep c0 o.lam (J + 1)).2 o.p P).2 o.e nE).2 o.q N2).1,
    (dstep (dstep (dstep (dstep c0 o.lam (J + 1)).2 o.p P).2 o.e nE).2 o.q N2).2⟩

/-- The loop's bit: cleared on the row counter's carry. -/
def moreW : HW := .ifr 24 (.seq (.wr sMORE false) (.dec 24)) .skip

/-- **The odometer's step**: the binary word, then the four counters on the carry, then the loop's bit. -/
def advW : HW :=
  .seq binIncW (.seq (.ifr 24 (incUW sLAM sJJ) .skip) (.seq (.ifr 24 (incUW sPC sPP) .skip)
    (.seq (.ifr 24 (incUW sEC sEE) .skip) (.seq (.ifr 24 (incUW sQC sNN) .skip) moreW))))

theorem advW_spec (w : List Bool) (J P nE N2 lam p e q : ℕ) (m : Bool) (hlam : lam < J + 1) (hp : p < P)
    (he : e < nE) (hq : q < N2) (σ : HS) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hC : σ.st sCTR = w) (hR : σ.st sCR = List.replicate w.length true)
    (hLAM : σ.st sLAM = unary lam (J + 1)) (hJJ : σ.st sJJ = List.replicate J true)
    (hPC : σ.st sPC = unary p P) (hPP : σ.st sPP = List.replicate (P - 1) true)
    (hEC : σ.st sEC = unary e nE) (hEE : σ.st sEE = List.replicate (nE - 1) true)
    (hQC : σ.st sQC = unary q N2) (hNN : σ.st sNN = List.replicate (N2 - 1) true) (hM : σ.st sMORE = [m])
    (hcap : 1 ≤ cap) :
    ∃ τ n, n ≤ 7 * w.length + 15 * (J + 1 + P + nE + N2) + 100 ∧ WExec cap advW σ τ n ∧
      τ.st = Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
        σ.st sCTR (binSucc w))
        sLAM (unary (odoStep J P nE N2 (if lead w < w.length then 0 else 1) ⟨lam, p, e, q, 0⟩).lam (J + 1)))
        sPC (unary (odoStep J P nE N2 (if lead w < w.length then 0 else 1) ⟨lam, p, e, q, 0⟩).p P))
        sEC (unary (odoStep J P nE N2 (if lead w < w.length then 0 else 1) ⟨lam, p, e, q, 0⟩).e nE))
        sQC (unary (odoStep J P nE N2 (if lead w < w.length then 0 else 1) ⟨lam, p, e, q, 0⟩).q N2))
        sMORE [if (odoStep J P nE N2 (if lead w < w.length then 0 else 1) ⟨lam, p, e, q, 0⟩).c = 1 then false else m] ∧
      τ.val = (fun _ => 0) ∧ τ.cell = σ.cell := by
  set c0 := if lead w < w.length then 0 else 1 with hc0
  have hc0l : c0 ≤ 1 := by rw [hc0]; split_ifs <;> omega
  obtain ⟨τ0, s0, st0, val0, cell0, sh0⟩ := binIncW_spec cap w σ hC hR (hsh _) (hsh _) (hv _) hcap
  rw [← hc0] at val0
  obtain ⟨τ1, n1, hn1, s1, st1, val1, cell1, sh1⟩ := stepU_spec cap sLAM sJJ (by decide) lam (J + 1) c0 hc0l hlam τ0
    (by rw [st0]; simp [hLAM]) (by rw [st0]; simp [hJJ]) (by rw [sh0 _ (by decide) (by decide)]; exact hsh _)
    (by rw [sh0 _ (by decide) (by decide)]; exact hsh _) (by rw [val0]; simp) hcap
  obtain ⟨τ2, n2, hn2, s2, st2, val2, cell2, sh2⟩ := stepU_spec cap sPC sPP (by decide) p P
    (dstep c0 lam (J + 1)).2 (dstep_carry_le _ _ _) hp τ1
    (by rw [st1, st0]; simp [hPC]) (by rw [st1, st0]; simp [hPP])
    (by rw [sh1 _ (by decide) (by decide), sh0 _ (by decide) (by decide)]; exact hsh _)
    (by rw [sh1 _ (by decide) (by decide), sh0 _ (by decide) (by decide)]; exact hsh _) (by rw [val1]; simp) hcap
  obtain ⟨τ3, n3, hn3, s3, st3, val3, cell3, sh3⟩ := stepU_spec cap sEC sEE (by decide) e nE
    (dstep (dstep c0 lam (J + 1)).2 p P).2 (dstep_carry_le _ _ _) he τ2
    (by rw [st2, st1, st0]; simp [hEC]) (by rw [st2, st1, st0]; simp [hEE])
    (by rw [sh2 _ (by decide) (by decide), sh1 _ (by decide) (by decide), sh0 _ (by decide) (by decide)]; exact hsh _)
    (by rw [sh2 _ (by decide) (by decide), sh1 _ (by decide) (by decide), sh0 _ (by decide) (by decide)]; exact hsh _)
    (by rw [val2]; simp) hcap
  obtain ⟨τ4, n4, hn4, s4, st4, val4, cell4, sh4⟩ := stepU_spec cap sQC sNN (by decide) q N2
    (dstep (dstep (dstep c0 lam (J + 1)).2 p P).2 e nE).2 (dstep_carry_le _ _ _) hq τ3
    (by rw [st3, st2, st1, st0]; simp [hQC]) (by rw [st3, st2, st1, st0]; simp [hNN])
    (by rw [sh3 _ (by decide) (by decide), sh2 _ (by decide) (by decide), sh1 _ (by decide) (by decide),
      sh0 _ (by decide) (by decide)]; exact hsh _)
    (by rw [sh3 _ (by decide) (by decide), sh2 _ (by decide) (by decide), sh1 _ (by decide) (by decide),
      sh0 _ (by decide) (by decide)]; exact hsh _)
    (by rw [val3]; simp) hcap
  set c4 := (dstep (dstep (dstep (dstep c0 lam (J + 1)).2 p P).2 e nE).2 q N2).2 with hc4
  have v4 : τ4.val 24 = c4 := by rw [val4]; simp
  have hM4 : τ4.st sMORE = [m] := by rw [st4, st3, st2, st1, st0]; simp [hM]
  have hMh : τ4.sh sMORE = 0 := by
    rw [sh4 _ (by decide) (by decide), sh3 _ (by decide) (by decide), sh2 _ (by decide) (by decide),
      sh1 _ (by decide) (by decide), sh0 _ (by decide) (by decide)]; exact hsh _
  have hv4 : ∀ r, r ≠ 24 → τ4.val r = 0 := by
    intro r hr
    rw [val4, val3, val2, val1, val0]
    simp [Function.update_of_ne hr, hv]
  have hfin : ∃ τ5 n5, n5 ≤ 5 ∧ WExec cap moreW τ4 τ5 n5 ∧
      τ5.st = Function.update τ4.st sMORE [if c4 = 1 then false else m] ∧ τ5.val = (fun _ => 0) ∧
      τ5.cell = τ4.cell := by
    by_cases h1 : c4 = 1
    · have w1 := WExec.wr (cap := cap) sMORE false τ4
      have w2 := WExec.dec (cap := cap) 24
        (τ4.sets sMORE (writeTapeBit (τ4.st sMORE) (τ4.sh sMORE) false)) (by simp [v4, h1]; omega)
      refine ⟨_, _, ?_, WExec.ifrT (Q := WM.skip) (by rw [v4, h1]; decide) (WExec.seq w1 w2), ?_, ?_, ?_⟩
      · omega
      · simp [hM4, hMh, h1, writeTapeBit]
      · funext r
        simp only [WState.setv_val, WState.sets_val, Function.update_apply]
        split_ifs with h
        · subst h; rw [v4, h1]
        · exact hv4 r h
      · rfl
    · have h0 : c4 = 0 := by have := dstep_carry_le (dstep (dstep (dstep c0 lam (J + 1)).2 p P).2 e nE).2 q N2; omega
      refine ⟨τ4, 1, by omega, WExec.ifrF (P := WM.seq (WM.wr sMORE false) (WM.dec 24)) (by rw [v4, h0]) (WExec.skip _),
        ?_, ?_, rfl⟩
      · rw [if_neg h1, ← hM4, Function.update_eq_self]
      · funext r
        by_cases h : r = 24
        · subst h; rw [v4, h0]
        · exact hv4 r h
  obtain ⟨τ5, n5, hn5, s5, st5, val5, cell5⟩ := hfin
  refine ⟨τ5, _, ?_, WExec.seq s0 (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))), ?_, val5, ?_⟩
  · omega
  · rw [st5, st4, st3, st2, st1, st0]
    simp only [odoStep, hc4]
    funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rw [cell5, cell4, cell3, cell2, cell1, cell0]

end Adv

end NearCubicWires.WireExponent3_5.PrimT.HbM
