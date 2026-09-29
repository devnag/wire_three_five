import Proof.Wire_3_5.FinalPass.S5TSeed1

/-! # S5-THR, part 13: copying unary fields and records between streams (P3:2220-2231)

Stage 4's table builder reads `winWord M L J W` (`unary M ++ unary L ++ unary J ++ winRecs ++ [false]`); W6 leaves
`1^M`, `1^J` and `winRecs` on its ports. This module copies unary fields and records `1 1^a 0 1^b 0` from a stream
`P` onto a stream `O`, counting `P`'s moves in `K` and `O`'s cells in `KW` (so both heads can be returned later):

* `cSt` (the copy state: `u` appended to `O`, `P` and `K` advanced by `d`, `KW` by `|u|`) and its step lemmas;
* **`onesK_spec`**, **`fieldK_spec`** (`1^a 0`), **`recK_spec`** (a record, read in place), **`recsK_spec`**.

Paper quantity of the main types: the level records of the fixed hash's table (stage 4's input word). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

section Copy
variable (P O : Fin (ns + 1)) (K KW : Fin nr)

/-- One cell appended to `O`, counted in `KW`. -/
def emitK (b : Bool) : WM ns nr := .seq (emit1 O b) (.inc KW)

/-- The copy state: `u` appended to `O`, `P`'s head and `K` advanced by `d`, `KW` by `|u|`. -/
def cSt (σ : WState ns nr) (u : List Bool) (d : ℕ) : WState ns nr :=
  (((appW σ O u).seth P (σ.sh P + d)).setv K (σ.val K + d)).setv KW (σ.val KW + u.length)

variable {P O K KW}

theorem cSt_st (σ : WState ns nr) (u : List Bool) (d : ℕ) :
    (cSt P O K KW σ u d).st = Function.update σ.st O (σ.st O ++ u) := by simp [cSt]

theorem cSt_sh (σ : WState ns nr) (u : List Bool) (d : ℕ) (i : Fin (ns + 1)) :
    (cSt P O K KW σ u d).sh i = if i = P then σ.sh P + d else if i = O then (σ.st O).length + u.length
      else σ.sh i := by
  simp only [cSt, WState.setv_sh, WState.seth_sh, appW_sh, Function.update_apply]

theorem cSt_val (σ : WState ns nr) (u : List Bool) (d : ℕ) (r : Fin nr) :
    (cSt P O K KW σ u d).val r = if r = KW then σ.val KW + u.length else if r = K then σ.val K + d
      else σ.val r := by
  simp only [cSt, WState.setv_val, WState.seth_val, appW_val, Function.update_apply]

theorem cSt_cell (σ : WState ns nr) (u : List Bool) (d : ℕ) : (cSt P O K KW σ u d).cell = σ.cell := by
  simp [cSt]

theorem emitK_cSt (hPO : P ≠ O) (_hK : K ≠ KW) (σ : WState ns nr) (u : List Bool) (d : ℕ) (b : Bool)
    (hc : σ.val KW + u.length < cap) :
    WExec cap (emitK O KW b) (cSt P O K KW σ u d) (cSt P O K KW σ (u ++ [b]) d) 7 := by
  have hO' : (cSt P O K KW σ u d).sh O = ((cSt P O K KW σ u d).st O).length := by
    rw [cSt_sh, if_neg (Ne.symm hPO), if_pos rfl, cSt_st]; simp
  have e1 := emit1_spec cap O b (cSt P O K KW σ u d) hO'
  have hv : (appW (cSt P O K KW σ u d) O [b]).val KW = σ.val KW + u.length := by
    rw [appW_val, cSt_val, if_pos rfl]
  have e2 := WExec.inc (cap := cap) KW (appW (cSt P O K KW σ u d) O [b]) (by rw [hv]; omega)
  rw [hv] at e2
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext i
    simp only [WState.setv_sh, appW_sh, Function.update_apply, cSt_sh, cSt_st]
    split_ifs <;> simp_all <;> omega
  · funext i
    simp only [WState.setv_st, appW_st, cSt_st, Function.update_apply]
    split_ifs <;> simp_all
  · funext r
    simp only [WState.setv_val, appW_val, cSt_val, Function.update_apply]
    split_ifs <;> simp_all <;> omega
  · simp [cSt_cell]

theorem fwdK_cSt (hPO : P ≠ O) (hK : K ≠ KW) (σ : WState ns nr) (u : List Bool) (d : ℕ) (hc : σ.val K + d < cap) :
    WExec cap (.seq (.fwd P) (.inc K)) (cSt P O K KW σ u d) (cSt P O K KW σ u (d + 1)) 5 := by
  have e1 := WExec.fwd (cap := cap) P (cSt P O K KW σ u d)
  have hv : ((cSt P O K KW σ u d).seth P ((cSt P O K KW σ u d).sh P + 1)).val K = σ.val K + d := by
    rw [WState.seth_val, cSt_val, if_neg hK, if_pos rfl]
  have e2 := WExec.inc (cap := cap) K ((cSt P O K KW σ u d).seth P ((cSt P O K KW σ u d).sh P + 1))
    (by rw [hv]; omega)
  rw [hv] at e2
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext i
    simp only [WState.setv_sh, WState.seth_sh, Function.update_apply, cSt_sh]
    split_ifs <;> simp_all <;> omega
  · rfl
  · funext r
    simp only [WState.setv_val, WState.seth_val, Function.update_apply, cSt_val]
    split_ifs <;> simp_all <;> omega
  · rfl

end Copy

/-! ## Ones, fields, records -/

/-- The ones at `P`'s head copied onto `O`. -/
def onesK (P O : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr :=
  .whs P (.seq (emitK O KW true) (.seq (.fwd P) (.inc K)))

theorem onesK_spec (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (a : ℕ) (u : List Bool) (d : ℕ) :
    ∀ k, k ≤ a → (∀ i < k, readTapeBit (σ.st P) (σ.sh P + d + i) = true) →
      readTapeBit (σ.st P) (σ.sh P + d + k) = false → σ.val K + d + k ≤ cap → σ.val KW + u.length + k ≤ cap →
      WExec cap (onesK P O K KW) (cSt P O K KW σ u d)
        (cSt P O K KW σ (u ++ List.replicate k true) (d + k)) (15 * k + 1)
  | 0, _, _, hend, _, _ => by
    have hb : wbit (cSt P O K KW σ u d) P = false := by
      unfold wbit; rw [cSt_st, cSt_sh, if_pos rfl, Function.update_of_ne hPO]; simpa using hend
    rw [List.replicate_zero, List.append_nil, Nat.add_zero]
    exact WExec.mono (WExec.whsF hb) (by omega)
  | k + 1, hk, hones, hend, hc1, hc2 => by
    have hb : wbit (cSt P O K KW σ u d) P = true := by
      unfold wbit; rw [cSt_st, cSt_sh, if_pos rfl, Function.update_of_ne hPO]
      simpa using hones 0 (by omega)
    have e1 := emitK_cSt cap hPO hK σ u d true (by omega)
    have e2 := fwdK_cSt cap hPO hK σ (u ++ [true]) d (by omega)
    have ih := onesK_spec P O hPO K KW hK σ a (u ++ [true]) (d + 1) k (by omega)
      (fun i hi => by rw [show σ.sh P + (d + 1) + i = σ.sh P + d + (i + 1) by omega]; exact hones (i + 1) (by omega))
      (by rw [show σ.sh P + (d + 1) + k = σ.sh P + d + (k + 1) by omega]; exact hend)
      (by omega) (by simp; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih) ?_ (by omega)
    rw [List.append_assoc, show [true] ++ List.replicate k true = List.replicate (k + 1) true from rfl,
      show d + 1 + k = d + (k + 1) by omega]

/-- A unary field `1^a 0` copied (the `0` included), `P` past it. -/
def fieldK (P O : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr :=
  .seq (onesK P O K KW) (.seq (emitK O KW false) (.seq (.fwd P) (.inc K)))

theorem fieldK_spec (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (a : ℕ) (u : List Bool) (d : ℕ)
    (hones : ∀ i < a, readTapeBit (σ.st P) (σ.sh P + d + i) = true)
    (hend : readTapeBit (σ.st P) (σ.sh P + d + a) = false) (hc1 : σ.val K + d + a + 1 ≤ cap)
    (hc2 : σ.val KW + u.length + a + 1 ≤ cap) :
    WExec cap (fieldK P O K KW) (cSt P O K KW σ u d)
      (cSt P O K KW σ (u ++ (List.replicate a true ++ [false])) (d + a + 1)) (15 * a + 15) := by
  have e1 := onesK_spec cap P O hPO K KW hK σ a u d a le_rfl hones hend (by omega) (by omega)
  have e2 := emitK_cSt cap hPO hK σ (u ++ List.replicate a true) (d + a) false (by simp; omega)
  have e3 := fwdK_cSt cap hPO hK σ (u ++ List.replicate a true ++ [false]) (d + a) (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (by rw [List.append_assoc]) (by omega)

/-- Reading in place. -/
theorem rd_drop (l : List Bool) (h i : ℕ) : readTapeBit l (h + i) = (l.drop h).getD i false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem reads_rep (l rest : List Bool) (h a : ℕ) (hd : l.drop h = List.replicate a true ++ false :: rest) :
    (∀ i < a, readTapeBit l (h + i) = true) ∧ readTapeBit l (h + a) = false := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [rd_drop, hd, List.getD_append _ _ _ _ (by simpa using hi)]; simp [hi]
  · rw [rd_drop, hd, List.getD_append_right _ _ _ _ (by simp)]; simp

theorem rd_drop0 (l : List Bool) (h : ℕ) : readTapeBit l h = (l.drop h).getD 0 false := by
  have e := rd_drop l h 0
  rwa [Nat.add_zero] at e

/-- A record `1 1^a 0 1^b 0` as a pair `(a, b)`. -/
def recW (r : ℕ × ℕ) : List Bool := true :: (List.replicate r.1 true ++ false :: (List.replicate r.2 true ++ [false]))

theorem recW_length (r : ℕ × ℕ) : (recW r).length = r.1 + r.2 + 3 := by simp [recW]; omega

/-- One record copied. -/
def recK (P O : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr :=
  .seq (emitK O KW true) (.seq (.seq (.fwd P) (.inc K)) (.seq (fieldK P O K KW) (fieldK P O K KW)))

theorem recK_spec (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (a b : ℕ) (u : List Bool) (d : ℕ) (rest : List Bool)
    (hd : (σ.st P).drop (σ.sh P + d) = recW (a, b) ++ rest)
    (hc1 : σ.val K + d + (a + b + 3) ≤ cap) (hc2 : σ.val KW + u.length + (a + b + 3) ≤ cap) :
    WExec cap (recK P O K KW) (cSt P O K KW σ u d) (cSt P O K KW σ (u ++ recW (a, b)) (d + (a + b + 3)))
      (15 * (a + b) + 45) := by
  have hd1 : (σ.st P).drop (σ.sh P + (d + 1)) = List.replicate a true ++ false ::
      (List.replicate b true ++ false :: rest) := by
    rw [show σ.sh P + (d + 1) = σ.sh P + d + 1 by omega, ← List.drop_drop, hd]
    simp [recW]
  have hd2 : (σ.st P).drop (σ.sh P + (d + 1 + a + 1)) = List.replicate b true ++ false :: rest := by
    rw [show σ.sh P + (d + 1 + a + 1) = σ.sh P + (d + 1) + (a + 1) by omega, ← List.drop_drop, hd1,
      show List.replicate a true ++ false :: (List.replicate b true ++ false :: rest) =
        (List.replicate a true ++ [false]) ++ (List.replicate b true ++ false :: rest) by simp,
      List.drop_left' (by simp)]
  obtain ⟨r1, r2⟩ := reads_rep (σ.st P) _ (σ.sh P + (d + 1)) a hd1
  obtain ⟨q1, q2⟩ := reads_rep (σ.st P) _ (σ.sh P + (d + 1 + a + 1)) b hd2
  have e1 := emitK_cSt cap hPO hK σ u d true (by omega)
  have e2 := fwdK_cSt cap hPO hK σ (u ++ [true]) d (by omega)
  have e3 := fieldK_spec cap P O hPO K KW hK σ a (u ++ [true]) (d + 1)
    (fun i hi => by rw [show σ.sh P + (d + 1) + i = σ.sh P + (d + 1) + i from rfl]; exact r1 i hi)
    (by simpa [Nat.add_assoc] using r2) (by omega) (by simp; omega)
  have e4 := fieldK_spec cap P O hPO K KW hK σ b (u ++ [true] ++ (List.replicate a true ++ [false]))
    (d + 1 + a + 1) (fun i hi => q1 i hi) (by simpa [Nat.add_assoc] using q2) (by omega) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  rw [show d + 1 + a + 1 + b + 1 = d + (a + b + 3) by omega]
  congr 1
  simp [recW, List.append_assoc]

/-- The records' word. -/
def recsW (rs : List (ℕ × ℕ)) : List Bool := rs.flatMap recW

/-- The records copied (until a `0` at the head). -/
def recsK (P O : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr := .whs P (recK P O K KW)

/-- The records' cost. -/
def recsCost : List (ℕ × ℕ) → ℕ
  | [] => 1
  | r :: rs => 15 * (r.1 + r.2) + 47 + recsCost rs

theorem recsK_spec (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (rest : List Bool) (hrest : rest.getD 0 false = false) :
    ∀ (rs : List (ℕ × ℕ)) (u : List Bool) (d : ℕ), (σ.st P).drop (σ.sh P + d) = recsW rs ++ rest →
      σ.val K + d + (recsW rs).length ≤ cap → σ.val KW + u.length + (recsW rs).length ≤ cap →
      WExec cap (recsK P O K KW) (cSt P O K KW σ u d)
        (cSt P O K KW σ (u ++ recsW rs) (d + (recsW rs).length)) (recsCost rs)
  | [], u, d, hd, _, _ => by
    have hb : wbit (cSt P O K KW σ u d) P = false := by
      unfold wbit; rw [cSt_st, cSt_sh, if_pos rfl, Function.update_of_ne hPO, rd_drop0, hd]; simpa [recsW] using hrest
    simp only [recsW, List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero]
    exact WExec.whsF hb
  | (a, b) :: rs, u, d, hd, hc1, hc2 => by
    have hl : (recsW ((a, b) :: rs)).length = (a + b + 3) + (recsW rs).length := by
      rw [show recsW ((a, b) :: rs) = recW (a, b) ++ recsW rs from rfl, List.length_append, recW_length]
    have hb : wbit (cSt P O K KW σ u d) P = true := by
      unfold wbit; rw [cSt_st, cSt_sh, if_pos rfl, Function.update_of_ne hPO, rd_drop0, hd]; simp [recsW, recW]
    have e1 := recK_spec cap P O hPO K KW hK σ a b u d (recsW rs ++ rest)
      (by rw [hd]; simp [recsW, List.append_assoc]) (by omega) (by omega)
    have ih := recsK_spec P O hPO K KW hK σ rest hrest rs (u ++ recW (a, b)) (d + (a + b + 3))
      (by rw [show σ.sh P + (d + (a + b + 3)) = σ.sh P + d + (a + b + 3) by omega, ← List.drop_drop, hd]
          rw [show recsW ((a, b) :: rs) = recW (a, b) ++ recsW rs from rfl, List.append_assoc,
            List.drop_left' (by rw [recW_length])])
      (by omega) (by rw [List.length_append, recW_length]; omega)
    refine WExec.cast cap (WExec.whsT hb e1 ih) ?_ (by simp only [recsCost]; omega)
    rw [hl, List.append_assoc, show d + (a + b + 3) + (recsW rs).length = d + (a + b + 3 + (recsW rs).length) by omega]
    rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
