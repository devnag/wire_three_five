import Proof.Wire_3_5.Primitive.SeedFix.HbAdv

/-! # C4.Hb, machine part 12: the cell's validity (`filt:soft`, P3:2253-2290)

A cell `(q, e, p, λ, ι, γ)` prints a term only when its positions `ι_r` lie in the population `p` ("labels in
`L_j`", P3:2262-2266) and, at the terminal level `λ = J` ("The terminal counts are handled in the same way",
P3:2272), when `γ = 0` and `ι` is constant (`validOf`, HashRefM). The validity program computes that bit on `VAL`:
the population's length `L_p` (`lpW`), the sign pass (`gpW`), and the position pass (`ipW`), each check clearing
`VAL`.

Paper quantity of the main type (**`valW_spec`**): the cell's validity bit `validB`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

section Count
variable {ns nr : ℕ} (cap : ℕ)

/-- Count the elements of a population record into `K` (moves counted in `C`). -/
def cntElemsW (S : Fin (ns + 1)) (C K : Fin nr) : WM ns nr := .whs S (.seq (skipElemC S C) (.inc K))

theorem cntElems_spec (S : Fin (ns + 1)) (C K : Fin nr) (hCK : C ≠ K) (rest : List Bool) :
    ∀ (gis : List ℕ) (pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (gis.flatMap elemW ++ false :: rest) →
      σ.sh S = pre.length → σ.val C + (gis.flatMap elemW).length ≤ cap → σ.val K + gis.length < cap + 1 →
      WExec cap (cntElemsW S C K) σ
        (((σ.seth S (pre.length + (gis.flatMap elemW).length)).setv C (σ.val C + (gis.flatMap elemW).length)).setv K
          (σ.val K + gis.length)) (12 * (gis.flatMap elemW).length + 1)
  | [], pre, σ, hS, hh, _, _ => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd_app0]
    have e : ((σ.seth S (pre.length + (([] : List ℕ).flatMap elemW).length)).setv C
        (σ.val C + (([] : List ℕ).flatMap elemW).length)).setv K (σ.val K + ([] : List ℕ).length) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hh, wseth_same, wsetv_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by simp)
  | gi :: gis, pre, σ, hS, hh, hc, hk => by
    simp only [List.flatMap_cons, List.length_append] at hc
    simp only [List.length_cons] at hk
    have hw : wbit σ S = true := by simp [wbit, hS, hh, rd_app0, elemW]
    have s1 := skipElemC_spec cap S C gi pre (gis.flatMap elemW ++ false :: rest) σ (by simp [hS]) hh (by omega)
    set σ1 := (σ.seth S (pre.length + (elemW gi).length)).setv C (σ.val C + (elemW gi).length) with hσ1
    have v1C : σ1.val C = σ.val C + (elemW gi).length := by
      simp only [σ1, WState.setv_val, WState.seth_val, Function.update_self]
    have v1K : σ1.val K = σ.val K := by
      simp only [σ1, WState.setv_val, WState.seth_val]; rw [Function.update_of_ne (Ne.symm hCK)]
    have s2 := WExec.inc (cap := cap) K σ1 (by rw [v1K]; omega)
    have ih := cntElems_spec S C K hCK rest gis (pre ++ elemW gi) (σ1.setv K (σ1.val K + 1))
      (by simp only [σ1, WState.setv_st, WState.seth_st, hS, List.flatMap_cons, List.append_assoc])
      (by simp only [σ1, WState.setv_sh, WState.seth_sh, Function.update_self, List.length_append])
      (by rw [WState.setv_val, Function.update_of_ne hCK, v1C]; omega)
      (by rw [WState.setv_val, Function.update_self, v1K]; omega)
    have hl := elemW_length gi
    refine WExec.cast cap (WExec.whsT hw (WExec.seq s1 s2) ih) ?_ ?_
    · simp only [List.flatMap_cons, List.length_append, List.length_cons]
      wst
      all_goals (try simp_all) <;> omega
    · simp only [List.flatMap_cons, List.length_append]; omega

end Count

section Lp
variable (cap : ℕ)

theorem len_le_flat : ∀ gis : List ℕ, gis.length ≤ (gis.flatMap elemW).length
  | [] => le_refl _
  | gi :: gis => by
    have := len_le_flat gis
    rw [List.flatMap_cons, List.length_append, elemW_length, List.length_cons]; omega

/-- **The population's length** `L_p` into register `12`. -/
def lpW : HW := .seq (FinalPass.Hash4.wcopyR 11 18 22) (.seq (skipPopsC sPOPS 17 18) (.seq (WM.fwdC sPOPS 17)
  (.seq (WM.fwdC sPOPS 17) (cntElemsW sPOPS 17 12))))

theorem lpW_spec (p : ℕ) (pops : List (Bool × List ℕ)) (hp : p < pops.length) (σ : HS)
    (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0) (h11 : σ.val 11 = p) (h12 : σ.val 12 = 0)
    (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0) (h22 : σ.val 22 = 0) (hcap : (popsWord pops).length + p + 2 ≤ cap) :
    ∃ x y c, y ≤ (popsWord pops).length ∧
      c ≤ p * (9 * (popsWord pops).length + 20 + 4) + 12 * (popsWord pops).length + 18 * p + 40 ∧
      WExec cap lpW σ (((σ.seth sPOPS x).setv 17 y).setv 12 pops[p].2.length) c := by
  have hpw := popsWord_split pops p hp
  set rest := (pops.drop (p + 1)).flatMap popRec ++ [false] with hrest
  have hlen : (popsPre pops p).length + 2 + (pops[p].2.flatMap elemW).length + 1 ≤ (popsWord pops).length := by
    rw [hpw]; simp only [popRec, List.length_append, List.length_cons, List.length_nil]; omega
  have hgl : pops[p].2.length ≤ (pops[p].2.flatMap elemW).length := len_le_flat _
  have s1 := FinalPass.Hash4.wcopyR_spec cap 11 18 22 (by decide) (by decide) (by decide) σ h18 h22
    (by rw [h11]; omega)
  rw [h11] at s1
  have s2 := skipPopsC_spec cap sPOPS 17 18 (by decide) pops p hp.le (σ.setv 18 p) (by simp [hP]) (by simp [hPh])
    (by simp) (by simp [h17]; omega) (by omega)
  set σ2 := (((σ.setv 18 p).seth sPOPS (popsPre pops p).length).setv 17 ((σ.setv 18 p).val 17 +
    (popsPre pops p).length)).setv 18 0 with hσ2
  have s3 := wfwdC_spec cap sPOPS 17 σ2 (by simp [σ2, h17]; omega)
  set σ3 := (σ2.seth sPOPS (σ2.sh sPOPS + 1)).setv 17 (σ2.val 17 + 1) with hσ3
  have s4 := wfwdC_spec cap sPOPS 17 σ3 (by simp [σ3, σ2, h17]; omega)
  set σ4 := (σ3.seth sPOPS (σ3.sh sPOPS + 1)).setv 17 (σ3.val 17 + 1) with hσ4
  have v4_17 : σ4.val 17 = (popsPre pops p).length + 2 := by simp [σ4, σ3, σ2, h17] <;> omega
  have v4_12 : σ4.val 12 = 0 := by simp [σ4, σ3, σ2, h12]
  have s5 := cntElems_spec cap sPOPS 17 12 (by decide) (rest.drop 0) pops[p].2
    (popsPre pops p ++ [true, pops[p].1]) σ4
    (by simp only [σ4, σ3, σ2, WState.setv_st, WState.seth_st, hP, hpw, popRec, List.drop_zero, hrest]
        simp [List.append_assoc])
    (by simp [σ4, σ3, σ2] <;> omega) (by rw [v4_17]; omega) (by rw [v4_12]; omega)
  refine ⟨(popsPre pops p).length + 2 + (pops[p].2.flatMap elemW).length,
    (popsPre pops p).length + 2 + (pops[p].2.flatMap elemW).length, _, by omega, ?_,
    WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (le_refl _)⟩
  · omega
  · simp only [σ4, σ3, σ2]
    wst
    all_goals (try simp_all) <;> omega

end Lp

section Checks
variable (cap : ℕ)

/-- Keep `VAL` iff the flag `E₁ < E₀` holds. -/
def chkW (E : Fin 6 ↪ Fin 40) : HW := .seq (PrimAsm.UnaryArith.gtFlagW E) (.ifr (E 2) (.dec (E 2)) (.wr sVAL false))

/-- Clear `VAL` iff the flag `E₁ < E₀` holds. -/
def chkNW (E : Fin 6 ↪ Fin 40) : HW :=
  .seq (PrimAsm.UnaryArith.gtFlagW E) (.ifr (E 2) (.seq (.dec (E 2)) (.wr sVAL false)) .skip)

theorem sets_same_st (σ : HS) (i : Fin 24) (l : List Bool) (h : σ.st i = l) : σ.sets i l = σ := by
  apply WState.eq
  · rfl
  · funext j; simp only [WState.sets_st, Function.update_apply]; split_ifs with hj
    · subst hj; exact h.symm
    · rfl
  · rfl
  · rfl

theorem chkW_spec (E : Fin 6 ↪ Fin 40) (σ : HS) (b : Bool) (hV : σ.st sVAL = [b]) (hVh : σ.sh sVAL = 0)
    (h2 : σ.val (E 2) = 0) (h3 : σ.val (E 3) = 0) (h4 : σ.val (E 4) = 0) (h5 : σ.val (E 5) = 0)
    (ha : σ.val (E 0) ≤ cap) (hb : σ.val (E 1) ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap (chkW E) σ (σ.sets sVAL [b && decide (σ.val (E 1) < σ.val (E 0))])
      (30 * σ.val (E 0) + 30 * σ.val (E 1) + 20 + 1 + 2) := by
  have s1 := PrimAsm.UnaryArith.gtFlagW_spec cap E σ h2 h3 h4 h5 ha hb hcap
  by_cases hlt : σ.val (E 1) < σ.val (E 0)
  · rw [if_pos hlt] at s1
    have s2 := WExec.dec (cap := cap) (E 2) (σ.setv (E 2) 1) (by simp; omega)
    refine WExec.cast cap (WExec.seq s1 (WExec.ifrT (Q := WM.wr sVAL false) (by simp) s2)) ?_ (by omega)
    simp only [hlt, decide_true, Bool.and_true]
    rw [sets_same_st σ sVAL [b] hV]
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs with h
    · subst h; simp [h2]
    · rfl
  · rw [if_neg hlt] at s1
    have s2 := WExec.wr (cap := cap) sVAL false (σ.setv (E 2) 0)
    refine WExec.cast cap (WExec.seq s1 (WExec.ifrF (P := WM.dec (E 2)) (by simp) s2)) ?_ (by omega)
    simp only [hlt, decide_false, Bool.and_false]
    apply WState.eq
    · rfl
    · funext j; simp only [WState.sets_st, WState.setv_st, WState.setv_sh, Function.update_apply]
      split_ifs with h
      · subst h; simp [hV, hVh, writeTapeBit]
      · rfl
    · funext r; simp only [WState.sets_val, WState.setv_val, Function.update_apply]; split_ifs with h
      · subst h; simp [h2]
      · rfl
    · rfl

theorem chkNW_spec (E : Fin 6 ↪ Fin 40) (σ : HS) (b : Bool) (hV : σ.st sVAL = [b]) (hVh : σ.sh sVAL = 0)
    (h2 : σ.val (E 2) = 0) (h3 : σ.val (E 3) = 0) (h4 : σ.val (E 4) = 0) (h5 : σ.val (E 5) = 0)
    (ha : σ.val (E 0) ≤ cap) (hb : σ.val (E 1) ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap (chkNW E) σ (σ.sets sVAL [b && !decide (σ.val (E 1) < σ.val (E 0))])
      (30 * σ.val (E 0) + 30 * σ.val (E 1) + 20 + 1 + 4) := by
  have s1 := PrimAsm.UnaryArith.gtFlagW_spec cap E σ h2 h3 h4 h5 ha hb hcap
  by_cases hlt : σ.val (E 1) < σ.val (E 0)
  · rw [if_pos hlt] at s1
    have s2 := WExec.dec (cap := cap) (E 2) (σ.setv (E 2) 1) (by simp; omega)
    have s3 := WExec.wr (cap := cap) sVAL false ((σ.setv (E 2) 1).setv (E 2) ((σ.setv (E 2) 1).val (E 2) - 1))
    refine WExec.cast cap (WExec.seq s1 (WExec.ifrT (Q := WM.skip) (by simp) (WExec.seq s2 s3))) ?_ (by omega)
    simp only [hlt, decide_true, Bool.not_true, Bool.and_false]
    apply WState.eq
    · rfl
    · funext j; simp only [WState.sets_st, WState.setv_st, WState.setv_sh, Function.update_apply]
      split_ifs with h
      · subst h; simp [hV, hVh, writeTapeBit]
      · rfl
    · funext r; simp only [WState.sets_val, WState.setv_val, Function.update_apply]; split_ifs with h
      · subst h; simp [h2]
      · rfl
    · rfl
  · rw [if_neg hlt] at s1
    refine WExec.cast cap (WExec.seq s1 (WExec.ifrF (P := WM.seq (WM.dec (E 2)) (WM.wr sVAL false)) (by simp)
      (WExec.skip _))) ?_ (by omega)
    simp only [hlt, decide_false, Bool.not_false, Bool.and_true]
    rw [sets_same_st σ sVAL [b] hV]
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs with h
    · subst h; simp [h2]
    · rfl

end Checks

section Gamma
variable (cap : ℕ)

/-- The sign pass's body: a set sign bit at the terminal level (`r₂₈ = 0`) clears `VAL`. -/
def gBodyW : HW := .seq (.ifs sCTR (.ifr 28 .skip (.wr sVAL false)) .skip) (.fwd sCTR)

/-- **The sign pass** over the `2t` sign bits. -/
def gpW : HW := .seq (FinalPass.Hash4.wcopyR 15 25 22) (.whr 25 (.seq (.dec 25) gBodyW))

/-- The sign pass's bit after `k` signs. -/
def gB (lt : Bool) (γs : List Bool) (k : ℕ) : Bool := lt || decide (∀ i < k, γs.getD i false = false)

theorem gB_succ (lt : Bool) (γs : List Bool) (k : ℕ) :
    gB lt γs (k + 1) = (gB lt γs k && (lt || !γs.getD k false)) := by
  unfold gB
  cases lt
  · simp only [Bool.false_or]
    by_cases h : γs.getD k false = true
    · have h1 : ¬ ∀ i < k + 1, γs.getD i false = false := fun hh => by
        have := hh k (by omega); rw [h] at this; exact Bool.noConfusion this
      rw [decide_eq_false h1, h]; simp
    · have hf : γs.getD k false = false := by simpa using h
      have e : (∀ i < k + 1, γs.getD i false = false) ↔ ∀ i < k, γs.getD i false = false := by
        constructor
        · intro hh i hi; exact hh i (by omega)
        · intro hh i hi
          by_cases hik : i = k
          · subst hik; exact hf
          · exact hh i (by omega)
      rw [show decide (∀ i < k + 1, γs.getD i false = false) = decide (∀ i < k, γs.getD i false = false) from
        decide_eq_decide.mpr e, hf]
      simp
  · simp

theorem gpW_spec (γs : List Bool) (T2 : ℕ) (hT : γs.length = T2) (lt : Bool) (σ : HS)
    (hC : ∀ k < T2, readTapeBit (σ.st sCTR) k = γs.getD k false) (hCh : σ.sh sCTR = 0)
    (hV : σ.st sVAL = [true]) (hVh : σ.sh sVAL = 0) (h28 : σ.val 28 = if lt then 1 else 0)
    (h15 : σ.val 15 = T2) (h22 : σ.val 22 = 0) (h25 : σ.val 25 = 0) (hcap : T2 ≤ cap) :
    WExec cap gpW σ ((σ.seth sCTR T2).sets sVAL [gB lt γs T2]) (18 * T2 + 3 + 1 + (T2 * (5 + 4) + 1)) := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ h25 h22
    (by rw [h15]; exact hcap)
  rw [h15] at s1
  let S : ℕ → HS := fun k => ((σ.seth sCTR k).sets sVAL [gB lt γs k]).setv 25 (T2 - k)
  have hS0 : S 0 = σ.setv 25 T2 := by
    have e0 : gB lt γs 0 = true := by simp [gB]
    simp only [S, e0, Nat.sub_zero]
    rw [← hCh, wseth_same, sets_same_st σ sVAL [true] hV]
  have hloop := UnionMachine.Round.wloop cap 25 gBodyW 5 T2 S (fun k _ => by simp [S]) hcap
    (fun k hk => by
      have hbit : wbit ((S k).setv 25 (T2 - k - 1)) sCTR = γs.getD k false := by
        simp only [wbit, S, WState.setv_st, WState.sets_st, WState.seth_st, WState.setv_sh, WState.sets_sh,
          WState.seth_sh, Function.update_self]
        rw [Function.update_of_ne (by decide)]
        exact hC k hk
      have v28 : ((S k).setv 25 (T2 - k - 1)).val 28 = if lt then 1 else 0 := by simp [S, h28]
      have eV : ((S k).setv 25 (T2 - k - 1)).st sVAL = [gB lt γs k] := by simp [S]
      have eVh : ((S k).setv 25 (T2 - k - 1)).sh sVAL = 0 := by
        simp [S, hVh]
      have hS1 : S (k + 1) = ((σ.seth sCTR (k + 1)).sets sVAL [gB lt γs k && (lt || !γs.getD k false)]).setv 25
          (T2 - (k + 1)) := by simp only [S, gB_succ]
      rw [hS1]
      cases hg : γs.getD k false
      · rw [hg] at hbit
        have s := WExec.seq (WExec.ifsF (P := WM.ifr 28 WM.skip (WM.wr sVAL false)) hbit (WExec.skip _))
          (WExec.fwd (cap := cap) sCTR _)
        refine WExec.cast cap s ?_ (by omega)
        simp only [S, Bool.not_false, Bool.or_true, Bool.and_true]
        wst
        all_goals (try simp_all)
      · rw [hg] at hbit
        cases lt
        · have s := WExec.seq (WExec.ifsT (Q := WM.skip) hbit (WExec.ifrF (P := WM.skip) (by rw [v28]; rfl)
            (WExec.wr (cap := cap) sVAL false _))) (WExec.fwd (cap := cap) sCTR _)
          refine WExec.cast cap s ?_ (by omega)
          simp only [S, Bool.not_true, Bool.or_false, Bool.and_false]
          wst
          all_goals (try simp_all [writeTapeBit])
        · have s := WExec.seq (WExec.ifsT (Q := WM.skip) hbit (WExec.ifrT (Q := WM.wr sVAL false)
            (by rw [v28]; decide) (WExec.skip _))) (WExec.fwd (cap := cap) sCTR _)
          refine WExec.cast cap s ?_ (by omega)
          have e1 : gB true γs k = true := by simp [gB]
          simp only [S, Bool.true_or, Bool.and_true, e1]
          wst
          all_goals (try simp_all))
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq s1 hloop) ?_ (le_refl _)
  simp only [S, Nat.sub_self]
  wst
  all_goals (try simp_all)

end Gamma

section Iota
variable (cap : ℕ)

def eL19 : Fin 6 ↪ Fin 40 := ⟨![12, 19, 30, 31, 32, 33], by decide⟩
def eL27 : Fin 6 ↪ Fin 40 := ⟨![12, 27, 30, 31, 32, 33], by decide⟩
def eA : Fin 6 ↪ Fin 40 := ⟨![27, 19, 30, 31, 32, 33], by decide⟩
def eB : Fin 6 ↪ Fin 40 := ⟨![19, 27, 30, 31, 32, 33], by decide⟩

/-- The position pass's bit after `k` positions. -/
def iB (lt : Bool) (L : ℕ) (ιs : List ℕ) (k : ℕ) : Bool :=
  decide (∀ i < k, ιs.getD i 0 < L ∧ (lt = true ∨ ιs.getD i 0 = ιs.getD 0 0))

theorem iB_one (lt : Bool) (L : ℕ) (ιs : List ℕ) : iB lt L ιs 1 = decide (ιs.getD 0 0 < L) := by
  unfold iB
  apply decide_eq_decide.mpr
  constructor
  · intro h; exact (h 0 (by omega)).1
  · intro h i hi
    have : i = 0 := by omega
    subst this; exact ⟨h, Or.inr rfl⟩

theorem iB_succ (lt : Bool) (L : ℕ) (ιs : List ℕ) (k : ℕ) :
    iB lt L ιs (k + 1) = (iB lt L ιs k && decide (ιs.getD k 0 < L) &&
      (lt || (!decide (ιs.getD 0 0 < ιs.getD k 0) && !decide (ιs.getD k 0 < ιs.getD 0 0)))) := by
  have key : (∀ i < k + 1, ιs.getD i 0 < L ∧ (lt = true ∨ ιs.getD i 0 = ιs.getD 0 0)) ↔
      (∀ i < k, ιs.getD i 0 < L ∧ (lt = true ∨ ιs.getD i 0 = ιs.getD 0 0)) ∧ ιs.getD k 0 < L ∧
        (lt = true ∨ ιs.getD k 0 = ιs.getD 0 0) := by
    constructor
    · intro h; exact ⟨fun i hi => h i (by omega), (h k (by omega)).1, (h k (by omega)).2⟩
    · rintro ⟨h1, h2, h3⟩ i hi
      by_cases hik : i = k
      · subst hik; exact ⟨h2, h3⟩
      · exact h1 i (by omega)
  unfold iB
  cases lt
  · rw [Bool.false_or, ← decide_not, ← decide_not, ← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_and]
    apply decide_eq_decide.mpr
    rw [key]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h3' : ιs.getD k 0 = ιs.getD 0 0 := by
        rcases h3 with h | h
        · exact absurd h Bool.false_ne_true
        · exact h
      exact ⟨⟨h1, h2⟩, by omega, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, Or.inr (by omega)⟩
  · rw [Bool.true_or, Bool.and_true, ← Bool.decide_and]
    apply decide_eq_decide.mpr
    rw [key]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, Or.inl rfl⟩

/-- Read `ι₀` into register `19` and check it against `L`. -/
def i0W : HW := .seq (FinalPass.Hash4.wcopyR 16 26 22) (.seq (readRawW sCTR 26 19 20 21) (chkW eL19))

/-- One later position: read `ι_r` into `27`, check it against `L`, at the terminal level against `ι₀`. -/
def iBodyW : HW := .seq (FinalPass.Hash4.wcopyR 16 26 22) (.seq (readRawW sCTR 26 27 20 21) (.seq (chkW eL27)
  (.seq (.ifr 28 .skip (.seq (chkNW eA) (chkNW eB))) (WM.clear 27))))

/-- **The position pass.** -/
def ipW : HW := .seq i0W (.seq (FinalPass.Hash4.wcopyR 15 25 22) (.seq (.dec 25) (.whr 25 (.seq (.dec 25) iBodyW))))

/-- A uniform bound on one position's cost. -/
def iCost (ℓ L : ℕ) : ℕ :=
  18 * ℓ + (1 + 3 + 1 + (ℓ * (36 * 2 ^ ℓ + 12 + 4) + 1 + 1 + (3 * 2 ^ ℓ + 1))) + 30 * L + 160 * 2 ^ ℓ + 120

theorem i0_spec (ℓ L ι0 : ℕ) (b : Bool) (hι0 : ι0 < 2 ^ ℓ) (σ : HS)
    (hF : ∀ m < ℓ, readTapeBit (σ.st sCTR) (σ.sh sCTR + m) = (binary ℓ ι0).getD m false)
    (hV : σ.st sVAL = [b]) (hVh : σ.sh sVAL = 0)
    (h12 : σ.val 12 = L) (h16 : σ.val 16 = ℓ) (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0)
    (h21 : σ.val 21 = 0) (h22 : σ.val 22 = 0) (h26 : σ.val 26 = 0) (h30 : σ.val 30 = 0) (h31 : σ.val 31 = 0)
    (h32 : σ.val 32 = 0) (h33 : σ.val 33 = 0) (hcapL : L + 1 ≤ cap) (hcap : ℓ + 2 ^ (ℓ + 1) + 1 ≤ cap) :
    ∃ c, c ≤ iCost ℓ L ∧ WExec cap i0W σ (((σ.seth sCTR (σ.sh sCTR + ℓ)).setv 19 ι0).sets sVAL
      [b && decide (ι0 < L)]) c := by
  have hpw2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hpw : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have s1 := FinalPass.Hash4.wcopyR_spec cap 16 26 22 (by decide) (by decide) (by decide) σ h26 h22 (by omega)
  rw [h16] at s1
  have s2 := readRawW_spec cap sCTR 26 19 20 21 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (σ.setv 26 ℓ) (binary ℓ ι0) (by simp [binary_length]) (by simp [h20]) (by simp [h21])
    (fun m hm => by rw [binary_length] at hm; simpa using hF m hm)
    (by simp [h19, binary_length]; omega)
  simp only [binary_length] at s2
  rw [bitsValue_binary, Nat.mod_eq_of_lt hι0] at s2
  set σ2 := (((σ.setv 26 ℓ).seth sCTR ((σ.setv 26 ℓ).sh sCTR + ℓ)).setv 19 ((σ.setv 26 ℓ).val 19 + ι0)).setv 26 0
    with hσ2
  have v2 : ∀ r : Fin 40, σ2.val r = if r = 19 then ι0 else σ.val r := by
    intro r; simp only [σ2, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have s3 := chkW_spec cap eL19 σ2 b (by simp [σ2, hV]) (by simp [σ2, hVh])
    (show σ2.val 30 = 0 by rw [v2, if_neg (by decide)]; exact h30)
    (show σ2.val 31 = 0 by rw [v2, if_neg (by decide)]; exact h31)
    (show σ2.val 32 = 0 by rw [v2, if_neg (by decide)]; exact h32)
    (show σ2.val 33 = 0 by rw [v2, if_neg (by decide)]; exact h33)
    (show σ2.val 12 ≤ cap by rw [v2, if_neg (by decide)]; omega)
    (show σ2.val 19 ≤ cap by rw [v2, if_pos rfl]; omega) (by omega)
  have e1 : σ2.val (eL19 1) = ι0 := show σ2.val 19 = ι0 by rw [v2, if_pos rfl]
  have e0 : σ2.val (eL19 0) = L := show σ2.val 12 = L by rw [v2, if_neg (by decide)]; exact h12
  rw [e1, e0] at s3
  refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (le_refl _)⟩
  · simp only [iCost]; omega
  · apply WState.eq
    · funext j; simp only [σ2, WState.sets_sh, WState.setv_sh, WState.seth_sh, Function.update_apply]
    · funext j; simp only [σ2, WState.sets_st, WState.setv_st, WState.seth_st, Function.update_apply]
    · funext r; simp only [WState.sets_val, WState.setv_val, WState.seth_val, Function.update_apply]
      rw [v2]
    · rfl

theorem tchk_spec (ι ι0 : ℕ) (lt v : Bool) (τ : HS) (hV : τ.st sVAL = [v]) (hVh : τ.sh sVAL = 0)
    (h19 : τ.val 19 = ι0) (h27 : τ.val 27 = ι) (h28 : τ.val 28 = if lt then 1 else 0) (h30 : τ.val 30 = 0)
    (h31 : τ.val 31 = 0) (h32 : τ.val 32 = 0) (h33 : τ.val 33 = 0) (hι : ι ≤ cap) (hι0 : ι0 ≤ cap) (hcap : 1 ≤ cap) :
    ∃ c, c ≤ 60 * ι + 60 * ι0 + 60 ∧ WExec cap (.ifr 28 .skip (.seq (chkNW eA) (chkNW eB))) τ
      (τ.sets sVAL [v && (lt || (!decide (ι0 < ι) && !decide (ι < ι0)))]) c := by
  cases lt
  · have u1 := chkNW_spec cap eA τ v hV hVh h30 h31 h32 h33 (show τ.val 27 ≤ cap by omega)
      (show τ.val 19 ≤ cap by omega) hcap
    have a1 : τ.val (eA 1) = ι0 := h19
    have a0 : τ.val (eA 0) = ι := h27
    rw [a1, a0] at u1
    set τ4 := τ.sets sVAL [v && !decide (ι0 < ι)] with hτ4
    have u2 := chkNW_spec cap eB τ4 (v && !decide (ι0 < ι)) (by simp [τ4]) (by simp [τ4, hVh])
      (show τ4.val 30 = 0 from h30) (show τ4.val 31 = 0 from h31) (show τ4.val 32 = 0 from h32)
      (show τ4.val 33 = 0 from h33) (show τ4.val 19 ≤ cap by simp only [τ4, WState.sets_val]; omega)
      (show τ4.val 27 ≤ cap by simp only [τ4, WState.sets_val]; omega) hcap
    have b1 : τ4.val (eB 1) = ι := h27
    have b0 : τ4.val (eB 0) = ι0 := h19
    rw [b1, b0] at u2
    refine ⟨_, ?_, WExec.cast cap (WExec.ifrF (P := WM.skip) h28 (WExec.seq u1 u2)) ?_ (le_refl _)⟩
    · omega
    · simp only [τ4, Bool.false_or]
      apply WState.eq <;> try rfl
      funext j; simp only [WState.sets_st, Function.update_apply]; split_ifs <;> simp [Bool.and_assoc]
  · refine ⟨1, by omega, WExec.cast cap (WExec.ifrT (Q := WM.seq (chkNW eA) (chkNW eB)) (by rw [h28]; decide)
      (WExec.skip _)) ?_ (le_refl _)⟩
    simp only [Bool.true_or, Bool.and_true]
    exact (sets_same_st τ sVAL _ hV).symm

theorem iBody_spec (ℓ L ι ι0 : ℕ) (lt v : Bool) (hι : ι < 2 ^ ℓ) (hι0 : ι0 < 2 ^ ℓ) (τ : HS)
    (hF : ∀ m < ℓ, readTapeBit (τ.st sCTR) (τ.sh sCTR + m) = (binary ℓ ι).getD m false)
    (hV : τ.st sVAL = [v]) (hVh : τ.sh sVAL = 0)
    (h12 : τ.val 12 = L) (h16 : τ.val 16 = ℓ) (h19 : τ.val 19 = ι0) (h20 : τ.val 20 = 0)
    (h21 : τ.val 21 = 0) (h22 : τ.val 22 = 0) (h26 : τ.val 26 = 0) (h27 : τ.val 27 = 0)
    (h28 : τ.val 28 = if lt then 1 else 0) (h30 : τ.val 30 = 0) (h31 : τ.val 31 = 0)
    (h32 : τ.val 32 = 0) (h33 : τ.val 33 = 0) (hcapL : L + 1 ≤ cap) (hcap : ℓ + 2 ^ (ℓ + 1) + 1 ≤ cap) :
    ∃ c, c ≤ iCost ℓ L ∧ WExec cap iBodyW τ ((τ.seth sCTR (τ.sh sCTR + ℓ)).sets sVAL
      [v && decide (ι < L) && (lt || (!decide (ι0 < ι) && !decide (ι < ι0)))]) c := by
  have hpw2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hpw : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have t1 := FinalPass.Hash4.wcopyR_spec cap 16 26 22 (by decide) (by decide) (by decide) τ h26 h22 (by omega)
  rw [h16] at t1
  have t2 := readRawW_spec cap sCTR 26 27 20 21 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (τ.setv 26 ℓ) (binary ℓ ι) (by simp [binary_length]) (by simp [h20]) (by simp [h21])
    (fun m hm => by rw [binary_length] at hm; simpa using hF m hm)
    (by simp [h27, binary_length]; omega)
  simp only [binary_length] at t2
  rw [bitsValue_binary, Nat.mod_eq_of_lt hι] at t2
  set τ2 := (((τ.setv 26 ℓ).seth sCTR ((τ.setv 26 ℓ).sh sCTR + ℓ)).setv 27 ((τ.setv 26 ℓ).val 27 + ι)).setv 26 0
    with hτ2
  have w2 : ∀ r : Fin 40, τ2.val r = if r = 27 then ι else τ.val r := by
    intro r; simp only [τ2, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have t3 := chkW_spec cap eL27 τ2 v (by simp [τ2, hV]) (by simp [τ2, hVh])
    (show τ2.val 30 = 0 by rw [w2, if_neg (by decide)]; exact h30)
    (show τ2.val 31 = 0 by rw [w2, if_neg (by decide)]; exact h31)
    (show τ2.val 32 = 0 by rw [w2, if_neg (by decide)]; exact h32)
    (show τ2.val 33 = 0 by rw [w2, if_neg (by decide)]; exact h33)
    (show τ2.val 12 ≤ cap by rw [w2, if_neg (by decide)]; omega)
    (show τ2.val 27 ≤ cap by rw [w2, if_pos rfl]; omega) (by omega)
  have f1 : τ2.val (eL27 1) = ι := show τ2.val 27 = ι by rw [w2, if_pos rfl]
  have f0 : τ2.val (eL27 0) = L := show τ2.val 12 = L by rw [w2, if_neg (by decide)]; exact h12
  rw [f1, f0] at t3
  set τ3 := τ2.sets sVAL [v && decide (ι < L)] with hτ3
  obtain ⟨c4, hc4, t4⟩ := tchk_spec cap ι ι0 lt (v && decide (ι < L)) τ3 (by simp [τ3]) (by simp [τ3, τ2, hVh])
    (show τ3.val 19 = ι0 by simp only [τ3, WState.sets_val]; rw [w2, if_neg (by decide)]; exact h19)
    (show τ3.val 27 = ι by simp only [τ3, WState.sets_val]; rw [w2, if_pos rfl])
    (show τ3.val 28 = _ by simp only [τ3, WState.sets_val]; rw [w2, if_neg (by decide)]; exact h28)
    (show τ3.val 30 = 0 by simp only [τ3, WState.sets_val]; rw [w2, if_neg (by decide)]; exact h30)
    (show τ3.val 31 = 0 by simp only [τ3, WState.sets_val]; rw [w2, if_neg (by decide)]; exact h31)
    (show τ3.val 32 = 0 by simp only [τ3, WState.sets_val]; rw [w2, if_neg (by decide)]; exact h32)
    (show τ3.val 33 = 0 by simp only [τ3, WState.sets_val]; rw [w2, if_neg (by decide)]; exact h33)
    (by omega) (by omega) (by omega)
  set τ4 := τ3.sets sVAL [v && decide (ι < L) && (lt || (!decide (ι0 < ι) && !decide (ι < ι0)))] with hτ4
  have v427 : τ4.val 27 = ι := by simp only [τ4, τ3, WState.sets_val]; rw [w2, if_pos rfl]
  have t5 := wclear_spec cap 27 ι τ4 v427 (by rw [v427]; omega)
  refine ⟨_, ?_, WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 t5)))) ?_ (le_refl _)⟩
  · simp only [iCost]; omega
  · apply WState.eq
    · funext j; simp only [τ4, τ3, τ2, WState.sets_sh, WState.setv_sh, WState.seth_sh, Function.update_apply]
    · funext j; simp only [τ4, τ3, τ2, WState.sets_st, WState.setv_st, WState.seth_st, Function.update_apply]
      split_ifs <;> rfl
    · funext r; simp only [τ4, τ3, WState.sets_val, WState.setv_val, WState.seth_val, Function.update_apply]
      rw [w2]
      split_ifs <;> (try subst_vars) <;> simp_all
    · rfl

theorem ipW_spec (γs : List Bool) (ιs : List ℕ) (ℓ T2 L : ℕ) (lt b : Bool) (hγ : γs.length = T2)
    (hι : ιs.length = T2) (hT : 1 ≤ T2) (hι2 : ∀ i ∈ ιs, i < 2 ^ ℓ) (σ : HS)
    (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hCh : σ.sh sCTR = T2) (hV : σ.st sVAL = [b]) (hVh : σ.sh sVAL = 0)
    (h12 : σ.val 12 = L) (h15 : σ.val 15 = T2) (h16 : σ.val 16 = ℓ) (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0)
    (h21 : σ.val 21 = 0) (h22 : σ.val 22 = 0) (h25 : σ.val 25 = 0) (h26 : σ.val 26 = 0) (h27 : σ.val 27 = 0)
    (h28 : σ.val 28 = if lt then 1 else 0) (h30 : σ.val 30 = 0) (h31 : σ.val 31 = 0) (h32 : σ.val 32 = 0)
    (h33 : σ.val 33 = 0) (hcapL : L + 1 ≤ cap) (hcap : T2 + ℓ + 2 ^ (ℓ + 1) + 1 ≤ cap) :
    ∃ c, c ≤ (T2 + 1) * (iCost ℓ L + 4) + 18 * T2 + 10 ∧
      WExec cap ipW σ ((((σ.seth sCTR (T2 + T2 * ℓ)).setv 19 (ιs.getD 0 0)).sets sVAL [b && iB lt L ιs T2])) c := by
  have hlt2 : ∀ k < T2, ιs.getD k 0 < 2 ^ ℓ := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hι2 _ (List.getElem_mem _)
  have hfield : ∀ k < T2, ∀ m < ℓ, readTapeBit (σ.st sCTR) (T2 + k * ℓ + m) = (binary ℓ (ιs.getD k 0)).getD m false := by
    intro k hk m hm; rw [hC, ← hγ]; exact ctrWord_field γs ιs ℓ k m (by omega) hm
  have hpw : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hpw2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  obtain ⟨c1, hc1, s1⟩ := i0_spec cap ℓ L (ιs.getD 0 0) b (hlt2 0 hT) σ
    (fun m hm => by rw [hCh]; have := hfield 0 hT m hm; simpa using this) hV hVh h12 h16 h19 h20 h21 h22 h26
    h30 h31 h32 h33 hcapL (by omega)
  rw [hCh, ← iB_one lt L ιs] at s1
  set σ3 := ((σ.seth sCTR (T2 + ℓ)).setv 19 (ιs.getD 0 0)).sets sVAL [b && iB lt L ιs 1] with hσ3
  have s4 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ3
    (by simp [σ3, h25]) (by simp [σ3, h22]) (by simp [σ3, h15]; omega)
  have v315 : σ3.val 15 = T2 := by simp [σ3, h15]
  rw [v315] at s4
  have s5 := WExec.dec (cap := cap) 25 (σ3.setv 25 T2) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at s5
  set σ5 := (σ3.setv 25 T2).setv 25 (T2 - 1) with hσ5
  have v5 : ∀ r : Fin 40, r ≠ 25 → σ5.val r = if r = 19 then ιs.getD 0 0 else σ.val r := by
    intro r hr; simp only [σ5, σ3, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply, if_neg hr]
  let S : ℕ → HS := fun k => ((σ5.seth sCTR (T2 + (k + 1) * ℓ)).sets sVAL [b && iB lt L ιs (k + 1)]).setv 25
    (T2 - 1 - k)
  have hS0 : S 0 = σ5 := by
    simp only [S, Nat.zero_add, Nat.one_mul, Nat.sub_zero]
    apply WState.eq
    · funext j; simp only [σ5, σ3, WState.setv_sh, WState.sets_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all
    · funext j; simp only [σ5, σ3, WState.setv_st, WState.sets_st, WState.seth_st, Function.update_apply]
      split_ifs <;> simp_all
    · funext r; simp only [σ5, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  have hloop := UnionMachine.Round.wloop cap 25 iBodyW (iCost ℓ L) (T2 - 1) S (fun k _ => by simp [S]) (by omega)
    (fun k hk => by
      set τ := (S k).setv 25 (T2 - 1 - k - 1) with hτ
      have vτ : ∀ r : Fin 40, r ≠ 25 → τ.val r = if r = 19 then ιs.getD 0 0 else σ.val r := by
        intro r hr; simp only [τ, S, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply,
          if_neg hr]; exact v5 r hr
      have hτC : τ.st sCTR = σ.st sCTR := by simp [τ, S, σ5, σ3]
      have hτCh : τ.sh sCTR = T2 + (k + 1) * ℓ := by simp [τ, S]
      obtain ⟨c, hc, sb⟩ := iBody_spec cap ℓ L (ιs.getD (k + 1) 0) (ιs.getD 0 0) lt (b && iB lt L ιs (k + 1))
        (hlt2 (k + 1) (by omega)) (hlt2 0 hT) τ
        (fun m hm => by rw [hτC, hτCh]; exact hfield (k + 1) (by omega) m hm)
        (by simp [τ, S]) (by simp [τ, S, σ5, σ3, hVh])
        (by rw [vτ 12 (by decide), if_neg (by decide)]; exact h12)
        (by rw [vτ 16 (by decide), if_neg (by decide)]; exact h16)
        (by rw [vτ 19 (by decide), if_pos rfl])
        (by rw [vτ 20 (by decide), if_neg (by decide)]; exact h20)
        (by rw [vτ 21 (by decide), if_neg (by decide)]; exact h21)
        (by rw [vτ 22 (by decide), if_neg (by decide)]; exact h22)
        (by rw [vτ 26 (by decide), if_neg (by decide)]; exact h26)
        (by rw [vτ 27 (by decide), if_neg (by decide)]; exact h27)
        (by rw [vτ 28 (by decide), if_neg (by decide)]; exact h28)
        (by rw [vτ 30 (by decide), if_neg (by decide)]; exact h30)
        (by rw [vτ 31 (by decide), if_neg (by decide)]; exact h31)
        (by rw [vτ 32 (by decide), if_neg (by decide)]; exact h32)
        (by rw [vτ 33 (by decide), if_neg (by decide)]; exact h33) hcapL (by omega)
      refine WExec.cast cap sb ?_ hc
      have hs : S (k + 1) = ((σ5.seth sCTR (T2 + (k + 1 + 1) * ℓ)).sets sVAL
          [b && (iB lt L ιs (k + 1) && decide (ιs.getD (k + 1) 0 < L) &&
            (lt || (!decide (ιs.getD 0 0 < ιs.getD (k + 1) 0) && !decide (ιs.getD (k + 1) 0 < ιs.getD 0 0))))]).setv 25
          (T2 - 1 - (k + 1)) := by simp only [S, iB_succ]
      rw [hs, hτCh]
      apply WState.eq
      · funext j; simp only [τ, S, WState.setv_sh, WState.sets_sh, WState.seth_sh, Function.update_apply]
        split_ifs <;> first | rfl | ring
      · funext j; simp only [τ, S, WState.setv_st, WState.sets_st, WState.seth_st, Function.update_apply]
        split_ifs <;> simp [Bool.and_assoc]
      · funext r; simp only [τ, S, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
        split_ifs <;> omega
      · rfl)
  rw [hS0] at hloop
  refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s4 (WExec.seq s5 hloop))) ?_ (le_refl _)⟩
  · have hm : (T2 - 1) * (iCost ℓ L + 4) ≤ T2 * (iCost ℓ L + 4) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · simp only [S]
    have e1 : T2 - 1 - (T2 - 1) = 0 := by omega
    have e2 : T2 - 1 + 1 = T2 := by omega
    rw [e1, e2]
    apply WState.eq
    · funext j; simp only [σ5, σ3, WState.setv_sh, WState.sets_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> first | rfl | ring
    · funext j; simp only [σ5, σ3, WState.setv_st, WState.sets_st, WState.seth_st, Function.update_apply]
      split_ifs <;> rfl
    · funext r; simp only [σ5, σ3, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl

end Iota

section Val
variable (cap : ℕ)

/-- The validity program's loads: `λ`, `J`, `p`, `2t`, `ℓ₀`. -/
def ldV : List (Fin 24 × Fin 40) := [(sLAM, 9), (sJJ, 10), (sPC, 11), (sTT, 15), (sLL, 16)]

/-- **The validity program** (WM1a): loads, `L_p`, the level flag, `VAL := T`, the sign pass, the position pass,
the clears. -/
def valW : HW := .seq (loadsW 26 ldV) (.seq lpW (.seq (PrimAsm.UnaryArith.gtFlagW gR) (.seq (.wr sVAL true)
  (.seq gpW (.seq ipW (clearsW (List.finRange 40)))))))

/-- **The cell's validity bit.** -/
def validB (L lam J : ℕ) (γs : List Bool) (ιs : List ℕ) : Bool :=
  gB (decide (lam < J)) γs γs.length && iB (decide (lam < J)) L ιs ιs.length

/-- The validity program's cost bound. -/
def valBound (lam J p T2 ℓ L P : ℕ) : ℕ :=
  5 * (16 * (lam + J + p + T2 + ℓ) + 15) + 1 + (p * (9 * P + 20 + 4) + 12 * P + 18 * p + 40) + 1 +
    (30 * J + 30 * lam + 20) + 1 + 1 + 1 + (18 * T2 + 3 + 1 + (T2 * (5 + 4) + 1)) + 1 +
    ((T2 + 1) * (iCost ℓ L + 4) + 18 * T2 + 10) + 1 + 40 * (3 * (lam + J + p + T2 + ℓ + P + 2 ^ ℓ + 1) + 2)

theorem valW_spec (γs : List Bool) (ιs : List ℕ) (pops : List (Bool × List ℕ)) (lam J p T2 ℓ : ℕ) (v0 : Bool)
    (hp : p < pops.length) (hγ : γs.length = T2) (hι : ιs.length = T2) (hT : 1 ≤ T2)
    (hι2 : ∀ i ∈ ιs, i < 2 ^ ℓ) (σ : HS) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hP : σ.st sPOPS = popsWord pops) (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hLAM : σ.st sLAM = unary lam (J + 1))
    (hJJ : σ.st sJJ = List.replicate J true) (hPC : σ.st sPC = unary p pops.length)
    (hTT : σ.st sTT = List.replicate T2 true) (hLL : σ.st sLL = List.replicate ℓ true) (hV : σ.st sVAL = [v0])
    (hcap : lam + J + p + T2 + ℓ + (popsWord pops).length + 2 ^ (ℓ + 1) + 4 ≤ cap) :
    ∃ τ c, c ≤ valBound lam J p T2 ℓ pops[p].2.length (popsWord pops).length ∧ WExec cap valW σ τ c ∧
      τ.st = Function.update σ.st sVAL [validB pops[p].2.length lam J γs ιs] ∧ τ.val = (fun _ => 0) ∧
      τ.cell = σ.cell := by
  have hpw : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hpw2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  set L := pops[p].2.length with hL
  have hLP : L + 1 ≤ (popsWord pops).length := by
    have hpw' := popsWord_split pops p hp
    have := len_le_flat pops[p].2
    have e : (popsWord pops).length = (popsPre pops p).length + ((popRec pops[p]).length +
        ((pops.drop (p + 1)).flatMap popRec ++ [false]).length) := by
      rw [hpw']; simp only [List.length_append]
    simp only [popRec, List.length_append, List.length_cons, List.length_nil] at e
    omega
  set lt := decide (lam < J) with hlt
  -- loads
  let vs : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, lam, p, 0, 0, 0, 0, 0, 0, 0, T2, ℓ, J, 0, 0, 0, 0, 0, 0]
  let rs : Fin 24 → List Bool := ![[], [], [], [], [], [], List.replicate (J + 1 - 1 - lam) false,
    List.replicate (pops.length - 1 - p) false, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
  have gz : ∀ n : ℕ, (List.replicate n false).getD 0 false = false := fun n => by cases n <;> rfl
  have hmem : ∀ y ∈ ldV, σ.st y.1 = List.replicate (vs y.1) true ++ rs y.1 ∧ (rs y.1).getD 0 false = false ∧
      σ.sh y.1 = 0 := by
    intro y hy
    simp only [ldV, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by rw [hLAM]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hJJ]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hPC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hTT]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hLL]; exact (List.append_nil _).symm, rfl, hsh _⟩
  have hsum : (ldV.map fun y => vs y.1).sum = lam + (J + (p + (T2 + (ℓ + 0)))) := rfl
  have s1 := loadsW_spec cap 26 vs rs ldV σ (by decide) (hv 26) hmem
    (fun r => by have := ldv_le_sum vs ldV r; rw [hsum] at this; rw [hv r]; omega)
  have hlc : ldCost vs ldV ≤ 5 * (16 * (lam + J + p + T2 + ℓ) + 15) := by
    have hb : ∀ y ∈ ldV, vs y.1 ≤ lam + J + p + T2 + ℓ := by
      intro y hy
      simp only [ldV, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · show lam ≤ _; omega
      · show J ≤ _; omega
      · show p ≤ _; omega
      · show T2 ≤ _; omega
      · show ℓ ≤ _; omega
    have := ldCost_le vs _ ldV hb
    have hl : ldV.length = 5 := rfl
    rw [hl] at this; exact this
  set σ1 : HS := ⟨σ.sh, σ.st, fun r => σ.val r + ldv vs ldV r, σ.cell⟩ with hσ1
  have e1 : ∀ r, σ1.val r = ldv vs ldV r := fun r => by simp [σ1, hv]
  -- L_p
  obtain ⟨x2, y2, c2, hy2, hc2, s2⟩ := lpW_spec cap p pops hp σ1 (by simp [σ1, hP]) (by simp [σ1, hsh])
    (by rw [e1]; rfl) (by rw [e1]; rfl) (by rw [e1]; rfl) (by rw [e1]; rfl) (by rw [e1]; rfl) (by omega)
  set σ2 := ((σ1.seth sPOPS x2).setv 17 y2).setv 12 L with hσ2
  have e2 : ∀ r : Fin 40, σ2.val r = if r = 12 then L else if r = 17 then y2 else ldv vs ldV r := by
    intro r; simp only [σ2, WState.setv_val, WState.seth_val, Function.update_apply, e1]
  -- the level flag
  have s3 := PrimAsm.UnaryArith.gtFlagW_spec cap gR σ2 (show σ2.val 28 = 0 by rw [e2]; rfl)
    (show σ2.val 29 = 0 by rw [e2]; rfl) (show σ2.val 30 = 0 by rw [e2]; rfl) (show σ2.val 31 = 0 by rw [e2]; rfl)
    (show σ2.val 10 ≤ cap by rw [e2]; show J + 0 ≤ cap; omega)
    (show σ2.val 9 ≤ cap by rw [e2]; show lam + 0 ≤ cap; omega) (by omega)
  have f9 : σ2.val (gR 1) = lam := show σ2.val 9 = lam by rw [e2]; rfl
  have f10 : σ2.val (gR 0) = J := show σ2.val 10 = J by rw [e2]; rfl
  rw [f9, f10] at s3
  set σ3 := σ2.setv (gR 2) (if lam < J then 1 else 0) with hσ3
  have e3 : ∀ r : Fin 40, σ3.val r = if r = 28 then (if lam < J then 1 else 0) else σ2.val r := by
    intro r; simp only [σ3, WState.setv_val, Function.update_apply]; rfl
  -- VAL := T
  have s4 := WExec.wr (cap := cap) sVAL true σ3
  have hV4 : writeTapeBit (σ3.st sVAL) (σ3.sh sVAL) true = [true] := by
    simp [σ3, σ2, σ1, hV, hsh, writeTapeBit]
  rw [hV4] at s4
  set σ4 := σ3.sets sVAL [true] with hσ4
  -- the sign pass
  have s5 := gpW_spec cap γs T2 hγ lt σ4
    (fun k hk => by
      have := ctrWord_sign γs ιs ℓ k (by omega)
      simpa [σ4, σ3, σ2, σ1, hC] using this)
    (by simp [σ4, σ3, σ2, σ1, hsh]) (by simp [σ4]) (by simp [σ4, σ3, σ2, σ1, hsh])
    (by rw [show σ4.val 28 = σ3.val 28 from rfl, e3, if_pos rfl, hlt]; by_cases h : lam < J <;> simp [h])
    (by rw [show σ4.val 15 = σ3.val 15 from rfl, e3, if_neg (by decide), e2]; rfl)
    (by rw [show σ4.val 22 = σ3.val 22 from rfl, e3, if_neg (by decide), e2]; rfl)
    (by rw [show σ4.val 25 = σ3.val 25 from rfl, e3, if_neg (by decide), e2]; rfl) (by omega)
  set σ5 := (σ4.seth sCTR T2).sets sVAL [gB lt γs T2] with hσ5
  have e5 : ∀ r, σ5.val r = σ3.val r := fun r => rfl
  -- the position pass
  obtain ⟨c6, hc6, s6⟩ := ipW_spec cap γs ιs ℓ T2 L lt (gB lt γs T2) hγ hι hT hι2 σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, hC]) (by simp [σ5]) (by simp [σ5]) (by simp [σ5, σ4, σ3, σ2, σ1, hsh])
    (by rw [e5, e3, if_neg (by decide), e2, if_pos rfl])
    (by rw [e5, e3, if_neg (by decide), e2]; rfl) (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by rw [e5, e3, if_neg (by decide), e2]; rfl) (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by rw [e5, e3, if_neg (by decide), e2]; rfl) (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by rw [e5, e3, if_neg (by decide), e2]; rfl) (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by rw [e5, e3, if_pos rfl, hlt]; by_cases h : lam < J <;> simp [h])
    (by rw [e5, e3, if_neg (by decide), e2]; rfl) (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by rw [e5, e3, if_neg (by decide), e2]; rfl) (by rw [e5, e3, if_neg (by decide), e2]; rfl)
    (by omega) (by omega)
  set σ6 := ((σ5.seth sCTR (T2 + T2 * ℓ)).setv 19 (ιs.getD 0 0)).sets sVAL [gB lt γs T2 && iB lt L ιs T2] with hσ6
  have hι0 : ιs.getD 0 0 < 2 ^ ℓ := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hι2 _ (List.getElem_mem _)
  have hv6 : ∀ r, σ6.val r ≤ lam + J + p + T2 + ℓ + (popsWord pops).length + 2 ^ ℓ + 1 := by
    intro r
    have hld := (ldv_le_sum vs ldV r)
    rw [hsum] at hld
    simp only [σ6, WState.sets_val, WState.setv_val, WState.seth_val, Function.update_apply]
    rw [e5, e3, e2]
    split_ifs <;> omega
  have s7 := clearsW_spec cap (List.finRange 40) σ6 (List.nodup_finRange 40) (fun r => by have := hv6 r; omega)
  have hcl := clCost_le σ6.val _ hv6 (List.finRange 40)
  rw [List.length_finRange] at hcl
  refine ⟨_, _, ?_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))),
    ?_, ?_, ?_⟩
  · unfold valBound; omega
  · funext j
    simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.sets_st, WState.setv_st, WState.seth_st, Function.update_apply]
    split_ifs with h
    · subst h; simp [validB, hγ, hι, hlt]
    · rfl
  · funext r; simp
  · rfl

end Val

end NearCubicWires.WireExponent3_5.PrimT.HbM
