import Proof.Wire_3_5.Primitive.SeedFix.HbRead

/-! # C4.Hb, machine part 5: the populations' records (P3:2253-2262)

A population is `(sgn, gis)`: its sign `Z^±` and its pool gates `gis = thrDigGis`. The Hb machine reads them
from the stream `popsWord pops`: per population the record `T sgn`, its gates as elements `T 1^{gi} F`, then `F`; the
list ends with `F`. Every move on the stream is counted in a register, so the stream can be returned to cell `0`
(C5's `WM.rewind`) and walked again for the next position of a moment tuple.

Programs: `skipUC` (a unary word), `skipElemC`, `skipElemsC` (the rest of a gate list), `skipPopC` (a record),
`skipPopsC` / `skipElemsNC` (`K` records / elements, C6's `wloop`), `readSgnC`, `readElemC` (C5's `WM.readU`).

Paper quantities of the main types: the population's sign and its `i`-th gate (`readSgnC_spec`, `readElemC_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-! ## The words -/

/-- A gate element `T 1^{gi} F`. -/
def elemW (gi : ℕ) : List Bool := true :: (List.replicate gi true ++ [false])

/-- A population's record `T sgn`, its gates, `F`. -/
def popRec (pop : Bool × List ℕ) : List Bool := [true, pop.1] ++ (pop.2.flatMap elemW ++ [false])

/-- **The populations' stream**. -/
def popsWord (pops : List (Bool × List ℕ)) : List Bool := pops.flatMap popRec ++ [false]

theorem elemW_length (gi : ℕ) : (elemW gi).length = gi + 2 := by simp [elemW]

section Walk
variable {ns nr : ℕ} (cap : ℕ)

/-- Skip a unary word `1^n 0`, counting the moves in `C`. -/
def skipUC (S : Fin (ns + 1)) (C : Fin nr) : WM ns nr := .seq (.whs S (WM.fwdC S C)) (WM.fwdC S C)

theorem skipUC_loop (S : Fin (ns + 1)) (C : Fin nr) (rest : List Bool) :
    ∀ (n : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (List.replicate n true ++ false :: rest) →
      σ.sh S = pre.length → σ.val C + n ≤ cap →
      WExec cap (.whs S (WM.fwdC S C)) σ ((σ.seth S (pre.length + n)).setv C (σ.val C + n)) (7 * n + 1)
  | 0, pre, σ, hS, hh, _ => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd_app0]
    have e : (σ.seth S (pre.length + 0)).setv C (σ.val C + 0) = σ := by
      simp only [Nat.add_zero, ← hh, wseth_same, wsetv_same]
    rw [e]; exact WExec.whsF hz
  | n + 1, pre, σ, hS, hh, hc => by
    have hw : wbit σ S = true := by simp [wbit, hS, hh, rd_app0, List.replicate_succ]
    have s1 := wfwdC_spec cap S C σ (by omega)
    have ih := skipUC_loop S C rest n (pre ++ [true]) ((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1))
      (by simp [hS, List.replicate_succ]) (by simp [hh]) (by simp; omega)
    refine WExec.cast cap (WExec.whsT hw s1 ih) ?_ (by omega)
    wst
    all_goals omega

theorem skipUC_spec (S : Fin (ns + 1)) (C : Fin nr) (n : ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (List.replicate n true ++ false :: rest)) (hh : σ.sh S = pre.length)
    (hc : σ.val C + n + 1 ≤ cap) :
    WExec cap (skipUC S C) σ ((σ.seth S (pre.length + (n + 1))).setv C (σ.val C + (n + 1))) (7 * n + 7) := by
  have s1 := skipUC_loop cap S C rest n pre σ hS hh (by omega)
  have s2 := wfwdC_spec cap S C ((σ.seth S (pre.length + n)).setv C (σ.val C + n)) (by simp; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  wst
  all_goals omega

/-- Skip one gate element. -/
def skipElemC (S : Fin (ns + 1)) (C : Fin nr) : WM ns nr := .seq (WM.fwdC S C) (skipUC S C)

theorem skipElemC_spec (S : Fin (ns + 1)) (C : Fin nr) (gi : ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (elemW gi ++ rest)) (hh : σ.sh S = pre.length) (hc : σ.val C + (elemW gi).length ≤ cap) :
    WExec cap (skipElemC S C) σ ((σ.seth S (pre.length + (elemW gi).length)).setv C (σ.val C + (elemW gi).length))
      (7 * gi + 13) := by
  rw [elemW_length] at hc ⊢
  have s1 := wfwdC_spec cap S C σ (by omega)
  have s2 := skipUC_spec cap S C gi (pre ++ [true]) rest ((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1))
    (by simp [hS, elemW]) (by simp [hh]) (by simp; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  wst
  all_goals omega

end Walk

section Walk2
variable {ns nr : ℕ} (cap : ℕ)

/-- Skip the rest of a gate list (up to its `F`). -/
def skipElemsC (S : Fin (ns + 1)) (C : Fin nr) : WM ns nr := .whs S (skipElemC S C)

theorem skipElemsC_spec (S : Fin (ns + 1)) (C : Fin nr) (rest : List Bool) :
    ∀ (gis : List ℕ) (pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (gis.flatMap elemW ++ false :: rest) →
      σ.sh S = pre.length → σ.val C + (gis.flatMap elemW).length ≤ cap →
      WExec cap (skipElemsC S C) σ
        ((σ.seth S (pre.length + (gis.flatMap elemW).length)).setv C (σ.val C + (gis.flatMap elemW).length))
        (9 * (gis.flatMap elemW).length + 1)
  | [], pre, σ, hS, hh, _ => by
    have hz : wbit σ S = false := by simp [wbit, hS, hh, rd_app0]
    have e : (σ.seth S (pre.length + (([] : List ℕ).flatMap elemW).length)).setv C
        (σ.val C + (([] : List ℕ).flatMap elemW).length) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hh, wseth_same, wsetv_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by simp)
  | gi :: gis, pre, σ, hS, hh, hc => by
    simp only [List.flatMap_cons, List.length_append] at hc
    have hw : wbit σ S = true := by simp [wbit, hS, hh, rd_app0, elemW]
    have s1 := skipElemC_spec cap S C gi pre (gis.flatMap elemW ++ false :: rest) σ (by simp [hS]) hh (by omega)
    have ih := skipElemsC_spec S C rest gis (pre ++ elemW gi)
      ((σ.seth S (pre.length + (elemW gi).length)).setv C (σ.val C + (elemW gi).length))
      (by simp [hS]) (by simp) (by simp only [WState.setv_val, Function.update_self]; omega)
    have hl := elemW_length gi
    refine WExec.cast cap (WExec.whsT hw s1 ih) ?_ ?_
    · simp only [List.flatMap_cons, List.length_append]; wst; all_goals omega
    · simp only [List.flatMap_cons, List.length_append]; omega

/-- Skip one population record. -/
def skipPopC (S : Fin (ns + 1)) (C : Fin nr) : WM ns nr :=
  .seq (WM.fwdC S C) (.seq (WM.fwdC S C) (.seq (skipElemsC S C) (WM.fwdC S C)))

theorem skipPopC_spec (S : Fin (ns + 1)) (C : Fin nr) (pop : Bool × List ℕ) (pre rest : List Bool)
    (σ : WState ns nr) (hS : σ.st S = pre ++ (popRec pop ++ rest)) (hh : σ.sh S = pre.length)
    (hc : σ.val C + (popRec pop).length ≤ cap) :
    WExec cap (skipPopC S C) σ ((σ.seth S (pre.length + (popRec pop).length)).setv C (σ.val C + (popRec pop).length))
      (9 * (popRec pop).length + 20) := by
  have hpl : (popRec pop).length = (pop.2.flatMap elemW).length + 3 := by
    simp only [popRec, List.length_append, List.length_cons, List.length_nil, List.length_singleton]; omega
  rw [hpl] at hc ⊢
  have s1 := wfwdC_spec cap S C σ (by omega)
  set σ1 := (σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1) with hσ1
  have s2 := wfwdC_spec cap S C σ1 (by simp [σ1]; omega)
  set σ2 := (σ1.seth S (σ1.sh S + 1)).setv C (σ1.val C + 1) with hσ2
  have s3 := skipElemsC_spec cap S C rest pop.2 (pre ++ [true, pop.1]) σ2
    (by simp [σ2, σ1, hS, popRec]) (by simp [σ2, σ1, hh]; try omega)
    (by simp only [hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_self]; omega)
  set σ3 := (σ2.seth S ((pre ++ [true, pop.1]).length + (pop.2.flatMap elemW).length)).setv C
    (σ2.val C + (pop.2.flatMap elemW).length) with hσ3
  have s4 := wfwdC_spec cap S C σ3
    (by simp only [hσ3, hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_self]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (by omega)
  rw [hσ3, hσ2, hσ1]
  wst
  all_goals omega

/-- The prefix of the first `k` records. -/
def popsPre (pops : List (Bool × List ℕ)) (k : ℕ) : List Bool := (pops.take k).flatMap popRec

theorem popsPre_succ (pops : List (Bool × List ℕ)) (k : ℕ) (hk : k < pops.length) :
    popsPre pops (k + 1) = popsPre pops k ++ popRec pops[k] := by
  unfold popsPre
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp

theorem popsWord_split (pops : List (Bool × List ℕ)) (k : ℕ) (hk : k < pops.length) :
    popsWord pops = popsPre pops k ++ (popRec pops[k] ++ ((pops.drop (k + 1)).flatMap popRec ++ [false])) := by
  unfold popsWord popsPre
  have h1 : pops.flatMap popRec = (pops.take k).flatMap popRec ++ (pops.drop k).flatMap popRec := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h1, List.drop_eq_getElem_cons hk, List.flatMap_cons]
  simp only [List.append_assoc]

/-- Skip `K` records from the start. -/
def skipPopsC (S : Fin (ns + 1)) (C K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (skipPopC S C))

theorem skipPopsC_spec (S : Fin (ns + 1)) (C K : Fin nr) (hCK : C ≠ K) (pops : List (Bool × List ℕ)) (n : ℕ)
    (hn : n ≤ pops.length) (σ : WState ns nr) (hS : σ.st S = popsWord pops) (hh : σ.sh S = 0) (hK : σ.val K = n)
    (hc : σ.val C + (popsWord pops).length ≤ cap) (hnc : n ≤ cap) :
    WExec cap (skipPopsC S C K) σ
      (((σ.seth S (popsPre pops n).length).setv C (σ.val C + (popsPre pops n).length)).setv K 0)
      (n * (9 * (popsWord pops).length + 20 + 4) + 1) := by
  let T : ℕ → WState ns nr := fun k =>
    ((σ.seth S (popsPre pops k).length).setv C (σ.val C + (popsPre pops k).length)).setv K (n - k)
  have hpre_le : ∀ k, (popsPre pops k).length ≤ (popsWord pops).length := by
    intro k; unfold popsPre popsWord
    have h1 : pops.flatMap popRec = (pops.take k).flatMap popRec ++ (pops.drop k).flatMap popRec := by
      rw [← List.flatMap_append, List.take_append_drop]
    rw [h1, List.length_append, List.length_append]; omega
  have hT0 : T 0 = σ := by
    have e1 : σ.seth S 0 = σ := by conv_lhs => rw [← hh]
                                   exact wseth_same σ S
    simp only [T, popsPre, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero, Nat.sub_zero, e1,
      wsetv_same]
    rw [← hK, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (skipPopC S C) (9 * (popsWord pops).length + 20) n T
    (fun k _ => by simp [T])
    hnc
    (fun k hk => by
      have hkl : k < pops.length := by omega
      have hrl : (popRec pops[k]).length ≤ (popsWord pops).length := by
        rw [popsWord_split pops k hkl]; simp only [List.length_append]; omega
      have s := skipPopC_spec cap S C pops[k] (popsPre pops k) ((pops.drop (k + 1)).flatMap popRec ++ [false])
        ((T k).setv K (n - k - 1)) (by simp [T, hS, popsWord_split pops k hkl]) (by simp [T])
        (by
          have h1 := hpre_le (k + 1)
          rw [popsPre_succ pops k hkl, List.length_append] at h1
          have h2 : ((T k).setv K (n - k - 1)).val C = σ.val C + (popsPre pops k).length := by
            simp [T, Function.update_apply, hCK]
          rw [h2]; omega)
      refine WExec.cast cap s ?_ (by omega)
      simp only [T, popsPre_succ pops k hkl, List.length_append]
      wst
      all_goals omega)
  rw [hT0] at hloop
  refine WExec.cast cap hloop ?_ (by omega)
  simp [T]

end Walk2

section Walk3
variable {ns nr : ℕ} (cap : ℕ)

/-- The prefix of the first `k` gate elements. -/
def gisPre (gis : List ℕ) (k : ℕ) : List Bool := (gis.take k).flatMap elemW

theorem gisPre_succ (gis : List ℕ) (k : ℕ) (hk : k < gis.length) :
    gisPre gis (k + 1) = gisPre gis k ++ elemW gis[k] := by
  unfold gisPre
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp

theorem gis_split (gis : List ℕ) (k : ℕ) (hk : k < gis.length) :
    gis.flatMap elemW = gisPre gis k ++ (elemW gis[k] ++ (gis.drop (k + 1)).flatMap elemW) := by
  unfold gisPre
  have h1 : gis.flatMap elemW = (gis.take k).flatMap elemW ++ (gis.drop k).flatMap elemW := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [h1, List.drop_eq_getElem_cons hk, List.flatMap_cons]

/-- Skip `K` gate elements. -/
def skipElemsNC (S : Fin (ns + 1)) (C K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (skipElemC S C))

theorem skipElemsNC_spec (S : Fin (ns + 1)) (C K : Fin nr) (hCK : C ≠ K) (gis : List ℕ) (n : ℕ)
    (hn : n ≤ gis.length) (pre rest : List Bool) (σ : WState ns nr) (hS : σ.st S = pre ++ (gis.flatMap elemW ++ rest))
    (hh : σ.sh S = pre.length) (hK : σ.val K = n) (hc : σ.val C + (gis.flatMap elemW).length ≤ cap) (hnc : n ≤ cap) :
    WExec cap (skipElemsNC S C K) σ
      (((σ.seth S (pre.length + (gisPre gis n).length)).setv C (σ.val C + (gisPre gis n).length)).setv K 0)
      (n * (7 * (gis.flatMap elemW).length + 13 + 4) + 1) := by
  let T : ℕ → WState ns nr := fun k =>
    ((σ.seth S (pre.length + (gisPre gis k).length)).setv C (σ.val C + (gisPre gis k).length)).setv K (n - k)
  have hpre_le : ∀ k, (gisPre gis k).length ≤ (gis.flatMap elemW).length := by
    intro k; unfold gisPre
    have h1 : gis.flatMap elemW = (gis.take k).flatMap elemW ++ (gis.drop k).flatMap elemW := by
      rw [← List.flatMap_append, List.take_append_drop]
    rw [h1, List.length_append]; omega
  have hT0 : T 0 = σ := by
    simp only [T, gisPre, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero, Nat.sub_zero, ← hh,
      wseth_same, wsetv_same]
    rw [← hK, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap K (skipElemC S C) (7 * (gis.flatMap elemW).length + 13) n T
    (fun k _ => by simp [T])
    hnc
    (fun k hk => by
      have hkl : k < gis.length := by omega
      have hel : gis[k] ≤ (gis.flatMap elemW).length := by
        rw [gis_split gis k hkl]; simp only [List.length_append, elemW_length]; omega
      have s := skipElemC_spec cap S C gis[k] (pre ++ gisPre gis k) ((gis.drop (k + 1)).flatMap elemW ++ rest)
        ((T k).setv K (n - k - 1)) (by simp [T, hS, gis_split gis k hkl]) (by simp [T])
        (by
          have h1 := hpre_le (k + 1)
          rw [gisPre_succ gis k hkl, List.length_append] at h1
          have h2 : ((T k).setv K (n - k - 1)).val C = σ.val C + (gisPre gis k).length := by
            simp [T, Function.update_apply, hCK]
          rw [h2]; omega)
      refine WExec.cast cap s ?_ (by omega)
      simp only [T, gisPre_succ gis k hkl, List.length_append]
      wst
      all_goals omega)
  rw [hT0] at hloop
  refine WExec.cast cap hloop ?_ (by omega)
  simp [T]

/-- Read the gate of the element at the head into `r` (`r += gi`). -/
def readElemC (S : Fin (ns + 1)) (C r : Fin nr) : WM ns nr := .seq (WM.fwdC S C) (WM.readU S C r)

theorem readElemC_spec (S : Fin (ns + 1)) (C r : Fin nr) (hCr : C ≠ r) (gi : ℕ) (pre rest : List Bool)
    (σ : WState ns nr) (hS : σ.st S = pre ++ (elemW gi ++ rest)) (hh : σ.sh S = pre.length)
    (hc : σ.val C + gi + 2 ≤ cap) (hr : σ.val r + gi ≤ cap) :
    WExec cap (readElemC S C r) σ
      (((σ.seth S (pre.length + (elemW gi).length)).setv C (σ.val C + (elemW gi).length)).setv r (σ.val r + gi))
      (11 * gi + 13) := by
  rw [elemW_length]
  have s1 := wfwdC_spec cap S C σ (by omega)
  have s2 := wreadU_spec cap S C r hCr gi ((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1))
    (fun k hk => by
      simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hS, hh]
      rw [show pre.length + 1 + k = (pre ++ [true]).length + k by simp]
      rw [show pre ++ (elemW gi ++ rest) = (pre ++ [true]) ++ (List.replicate gi true ++ false :: rest) by simp [elemW]]
      rw [rd_app, List.getD_append _ _ _ _ (by simpa using hk)]
      simp [hk])
    (by
      simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hS, hh]
      rw [show pre.length + 1 + gi = (pre ++ [true]).length + gi by simp]
      rw [show pre ++ (elemW gi ++ rest) = (pre ++ [true]) ++ (List.replicate gi true ++ false :: rest) by simp [elemW]]
      rw [rd_app]; simp [List.getD_append])
    (by simp; omega) (by simp [Function.update_apply, Ne.symm hCr]; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  wst
  all_goals omega

end Walk3

end NearCubicWires.WireExponent3_5.PrimT.HbM
