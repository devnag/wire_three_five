import Proof.Wire_3_5.UnionMachine.EwWin
import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins

/-! # C6, e/W_j, part 9: the window block and its records

"The level windows `W_j = 16t + 20(⌊√(t·B_*)⌋ + 1)/2^{⌊j/2⌋} + 20`" (filt:majorant, P3:2150-2157) as finalpass stage 4
reads them. From `t`, `B_*`, `J` in registers (kept) on a blank stream: the top record (`EwWin.winA`), the `J` level
records below it (`EwLevel.lvBody` in a flag loop), the head rewound, the scratch cleared: **`winW_spec`** (the stream
holds `winList t B J`, every register back). The records are the fixed hash's: **`winList_eq`**, and at the THR
call's numbers **`winList_winRecs`** (`= Joins.winRecs (Joins.thrMP M A B_* K)`).

Paper quantity of the main type: the fixed hash's level windows `W_j` (filt:majorant) as stage 4's records. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwRecs
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.EwLevel
open NearCubicWires.WireExponent3_5.UnionMachine.EwWin

/-! ## The records are the fixed hash's -/

theorem flat_rev (f : ℕ → List Bool) :
    ∀ J, ((List.range J).reverse).flatMap f = (List.range J).flatMap (fun i => f (J - 1 - i))
  | 0 => rfl
  | J + 1 => by
    have h1 : (List.range (J + 1)).reverse = J :: (List.range J).reverse := by simp [List.range_succ]
    rw [h1, List.flatMap_cons, flat_rev f J, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    apply congrArg₂ (· ++ ·) (by simp)
    apply congrArg₂ List.flatMap _ rfl
    funext i
    show f (J - 1 - i) = f (J + 1 - 1 - (i + 1))
    congr 1
    omega

/-- **The window records are the fixed hash's level records** (`levels J = J, …, 0`, `W'_J = 0`). -/
theorem winList_eq (t B J : ℕ) (Wf : ℕ → ℕ) (hW : ∀ j, Wf j = twOf t (Nat.sqrt (t * B)) j) :
    winList t B J = (FinalPass.ListEval.levels J).flatMap (FinalPass.Hash4.winRec J Wf) := by
  unfold winList FinalPass.ListEval.levels
  rw [flat_rev, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  have htop : FinalPass.Hash4.winRec J Wf (J + 1 - 1 - 0) = topRec := by
    have hc : Nat.clog 2 (2 * 0 + 1) = 0 := Nat.clog_one_right 2
    have e : J + 1 - 1 - 0 = J := by omega
    rw [e]
    simp only [FinalPass.Hash4.winRec, FinalPass.ListEval.topW, if_pos rfl, FinalPass.ListEval.pow, hc,
      FinalPass.ListEval.unary]
    rfl
  rw [htop]
  apply congrArg₂ (· ++ ·) rfl
  unfold recsDown
  apply List.flatMap_congr
  intro i hi
  have hi' : i < J := List.mem_range.mp hi
  have hne : J + 1 - 1 - (i + 1) ≠ J := by omega
  have e : J + 1 - 1 - (i + 1) = J - 1 - i := by omega
  have hne' : J - 1 - i ≠ J := by omega
  show recOf t (Nat.sqrt (t * B)) (J - 1 - i) = FinalPass.Hash4.winRec J Wf (J + 1 - 1 - (i + 1))
  rw [e]
  simp only [FinalPass.Hash4.winRec, FinalPass.ListEval.topW, if_neg hne', hW, recOf, FinalPass.ListEval.pow]

/-- **At the THR call's numbers** the records are `Joins.winRecs (Joins.thrMP M A B_* K)`. -/
theorem winList_winRecs (M A Bs K : ℕ) :
    winList (Primitive.listT A Bs K) Bs (Primitive.listJ A Bs K) =
      PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP M A Bs K) := by
  unfold PrimThrW.Joins.winRecs
  exact winList_eq _ _ _ _ (fun j => rfl)

/-! ## The window block -/

/-- The length of the records below the top. -/
theorem recsDown_length_bound (t s J : ℕ) :
    ∀ k, (recsDown t s J k).length ≤ k * (5 * twMax t s + 5)
  | 0 => by simp [recsDown]
  | k + 1 => by
    rw [recsDown_succ, List.length_append, recOf_length]
    have ih := recsDown_length_bound t s J k
    have h1 := twOf_le t s (J - 1 - k)
    have h2 := EwKit.pow_clog_le2 (2 * twOf t s (J - 1 - k) + 1) (by omega)
    have e : (k + 1) * (5 * twMax t s + 5) = k * (5 * twMax t s + 5) + (5 * twMax t s + 5) := by ring
    omega

section Win
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (W : Fin 32 ↪ Fin nr)

/-- **The window block**: the top record, `J` levels, the head rewound, the scratch cleared. -/
def winW : WM ns nr :=
  .seq (.seq (.seq (.seq (winA O W) (.whr (W 4) (lvBody O (W 28) (vmap.trans W)))) (WM.rewind O (W 28)))
    (WM.clear (W 22))) (WM.clear (W 3))

/-- The block's capacity need. -/
def winNeed (t B J : ℕ) : ℕ :=
  2 * (B * t + 2) * (B * t + 2) + t + B + J + 20 + (2 ^ (J + 1) + J + Nat.sqrt (B * t) +
    1000 * (t + Nat.sqrt (B * t) + 2) + 13 * twMax t (Nat.sqrt (B * t)) + 32 +
    (recsDown t (Nat.sqrt (B * t)) J J).length)

/-- The block's cost. -/
def winCost (t B J : ℕ) : ℕ :=
  1000 * (B * t + 2) * (B * t + 2) * (B * t + 2) + 40 * (B + 1) * (t + 1) + 20 * J + 100 +
    (J * (lvCost t (Nat.sqrt (B * t)) J + 2) + 1) + (5 * (4 + (recsDown t (Nat.sqrt (B * t)) J J).length) + 1) +
    (3 * (B * t + 1) + 1) + (3 * Nat.sqrt (B * t) + 1) + 4

theorem winW_spec (σ : WState ns nr) (t B J : ℕ) (h0 : σ.val (W 0) = t) (h1 : σ.val (W 1) = B)
    (h2 : σ.val (W 2) = J) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (W i) = 0) (hO : σ.st O = [])
    (hOh : σ.sh O = 0) (hcap : winNeed t B J ≤ cap) :
    ∃ n, WExec cap (winW O W) σ (σ.sets O (winList t B J)) n ∧ n ≤ winCost t B J := by
  have hW : ∀ i k : Fin 32, W i = W k ↔ i = k := fun i k => W.injective.eq_iff
  have v0 : (vmap.trans W) 0 = W 0 := rfl
  have v1 : (vmap.trans W) 1 = W 3 := rfl
  have v2 : (vmap.trans W) 2 = W 4 := rfl
  have z3 := hz 3 (by decide)
  have z4 := hz 4 (by decide)
  have z22 := hz 22 (by decide)
  have z28 := hz 28 (by decide)
  unfold winNeed at hcap
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt (B * t) := ⟨_, rfl⟩
  rw [← hs] at hcap
  have hBt : B * t + 1 ≤ 2 * (B * t + 2) * (B * t + 2) := by
    have key : ∀ x : ℕ, x + 1 ≤ 2 * (x + 2) * (x + 2) := fun x => by nlinarith
    exact key _
  have hJ0 : 0 < 2 ^ J := Nat.two_pow_pos J
  have hJ1 : 0 < 2 ^ (J + 1) := Nat.two_pow_pos (J + 1)
  obtain ⟨n1, c1, hn1⟩ := winA_spec cap O W σ t B J h0 h1 h2 hz hO hOh (by omega)
  obtain ⟨L, hL⟩ : ∃ L, L = (recsDown t s J J).length := ⟨_, rfl⟩
  rw [← hL] at hcap
  have hPC : ∀ i, (vmap.trans W) i ≠ W 28 := by
    intro i h
    simp only [Function.Embedding.trans_apply] at h
    have := W.injective h
    fin_cases i <;> simp [vmap] at this
  obtain ⟨T, hT⟩ : ∃ T, T = stTop O W σ t B J := ⟨_, rfl⟩
  rw [← hT] at c1
  have n422 : W 4 ≠ W 22 := by simp [hW]
  have n428 : W 4 ≠ W 28 := by simp [hW]
  have n43 : W 4 ≠ W 3 := by simp [hW]
  have n2228 : W 22 ≠ W 28 := by simp [hW]
  have n223 : W 22 ≠ W 3 := by simp [hW]
  have n283 : W 28 ≠ W 3 := by simp [hW]
  have T0 : T.val (W 0) = t := by simp [hT, stTop, hW, h0]
  have T3 : T.val (W 3) = s := by simp [hT, stTop, hW, hs]
  have T4 : T.val (W 4) = J := by simp [hT, stTop]
  have T22 : T.val (W 22) = B * t + 1 := by simp [hT, stTop, hW]
  have T28 : T.val (W 28) = 4 := by simp [hT, stTop, hW]
  have TO : T.st O = topRec := by simp [hT, stTop]
  have TOh : T.sh O = 4 := by simp [hT, stTop]
  have Tval : ∀ r, r ≠ W 22 → r ≠ W 3 → r ≠ W 28 → r ≠ W 4 → T.val r = σ.val r := by
    intro r a b c d
    simp [hT, stTop, Function.update_apply, a, b, c, d]
  have Tst : ∀ q, q ≠ O → T.st q = σ.st q := by intro q hq; simp [hT, stTop, hq]
  have Tsh : ∀ q, q ≠ O → T.sh q = σ.sh q := by intro q hq; simp [hT, stTop, hq]
  have Tcell : T.cell = σ.cell := by simp [hT, stTop]
  have e0 : stL O (W 28) (vmap.trans W) T topRec 4 t s J 0 = T := by
    apply WState.eq
    · funext q; by_cases hq : q = O
      · subst hq; simp [stL, recsDown, TOh, topRec]
      · simp [stL, hq]
    · funext q; by_cases hq : q = O
      · subst hq; simp [stL, recsDown, TO]
      · simp [stL, hq]
    · funext r
      simp only [stL, WState.setv_val, WState.sets_val, WState.seth_val, v2]
      by_cases h28 : r = W 28
      · subst h28; simp [recsDown, T28]
      · by_cases h4 : r = W 4
        · subst h4; simp [Function.update_apply, n428, T4]
        · simp [Function.update_apply, h28, h4]
    · simp [stL]
  rw [← e0] at c1
  have hvm : ∀ i : Fin 20, 3 ≤ i.val → 5 ≤ (vmap i).val ∧ (vmap i).val ≤ 21 := by decide
  have hzT : ∀ x : Fin 32, 5 ≤ x.val → x.val ≤ 21 → T.val (W x) = 0 := by
    intro x h5 h21
    have n22 : W x ≠ W 22 := by rw [Ne, hW]; intro h; subst h; simp at h21
    have n3 : W x ≠ W 3 := by rw [Ne, hW]; intro h; subst h; simp at h5
    have n28 : W x ≠ W 28 := by rw [Ne, hW]; intro h; subst h; simp at h21
    have n4 : W x ≠ W 4 := by rw [Ne, hW]; intro h; subst h; simp at h5
    rw [Tval _ n22 n3 n28 n4]
    exact hz x (by omega)
  have lp := PrimAsm.UnaryPow.flagLoop cap (W 4) (lvBody O (W 28) (vmap.trans W)) (lvCost t s J) J
    (stL O (W 28) (vmap.trans W) T topRec 4 t s J)
    (fun k hk => by simp [stL, v2, Function.update_apply, n428]; omega)
    (by simp [stL, v2, Function.update_apply, n428])
    (fun k hk => lvBody_spec cap O (W 28) (vmap.trans W) hPC T topRec 4 t s J k hk
      (by rw [v0]; exact T0) (by rw [v1]; exact T3)
      (fun i hi => by
        rw [Function.Embedding.trans_apply]
        exact hzT _ (hvm i hi).1 (hvm i hi).2)
      TO (by rw [TOh]; rfl) (by rw [← hL]; omega))
  obtain ⟨SJ, hSJ⟩ : ∃ S, S = stL O (W 28) (vmap.trans W) T topRec 4 t s J J := ⟨_, rfl⟩
  rw [← hSJ] at lp
  have S28 : SJ.val (W 28) = 4 + L := by simp [hSJ, stL, ← hL, topRec]
  have SOh : SJ.sh O = 4 + L := by simp [hSJ, stL, ← hL, topRec]
  have SO : SJ.st O = topRec ++ recsDown t s J J := by simp [hSJ, stL]
  have S4 : SJ.val (W 4) = 0 := by simp [hSJ, stL, v2, Function.update_apply, n428]
  have S22 : SJ.val (W 22) = B * t + 1 := by
    simp [hSJ, stL, v2, Function.update_apply, n2228, n422.symm, T22]
  have S3 : SJ.val (W 3) = s := by simp [hSJ, stL, v2, Function.update_apply, n283.symm, n43.symm, T3]
  have Sval : ∀ r, r ≠ W 28 → r ≠ W 4 → SJ.val r = T.val r := by
    intro r a b; simp [hSJ, stL, v2, Function.update_apply, a, b]
  have Sst : ∀ q, q ≠ O → SJ.st q = T.st q := by intro q hq; simp [hSJ, stL, hq]
  have Ssh : ∀ q, q ≠ O → SJ.sh q = T.sh q := by intro q hq; simp [hSJ, stL, hq]
  have Scell : SJ.cell = T.cell := by simp [hSJ, stL]
  have c2 := WExec.seq c1 lp
  have c3 := WExec.seq c2 (wrewind_spec cap O (W 28) (4 + L) SJ S28 (by omega))
  have c4 := WExec.seq c3 (wclear_spec cap (W 22) (B * t + 1) _ (by simp [n2228, S22])
    (by simp [n2228, S22]; omega))
  have c5 := WExec.seq c4 (wclear_spec cap (W 3) s _ (by simp [n223.symm, n283.symm, S3])
    (by simp [n223.symm, n283.symm, S3]; omega))
  refine ⟨_, WExec.cast cap c5 ?_ le_rfl, ?_⟩
  · clear c1 c2 c3 c4 c5 lp
    apply WState.eq
    · funext q; by_cases hq : q = O
      · subst hq; simp [SOh, hOh]
      · simp [hq, Ssh q hq, Tsh q hq]
    · funext q; by_cases hq : q = O
      · subst hq
        have hs' : s = Nat.sqrt (t * B) := by rw [hs, Nat.mul_comm]
        simp [SO, winList, hs']
      · simp [hq, Sst q hq, Tst q hq]
    · funext r
      simp only [WState.setv_val, WState.seth_val]
      by_cases a3 : r = W 3
      · subst a3; simp [z3]
      · by_cases a22 : r = W 22
        · subst a22; simp [a3, z22, n223]
        · by_cases a28 : r = W 28
          · subst a28; simp [Function.update_apply, a3, a22, z28, n283, n2228.symm]
          · by_cases a4 : r = W 4
            · subst a4; simp [Function.update_apply, a3, a22, a28, S4, z4]
            · simp [Function.update_apply, a3, a22, a28, Sval r a28 a4, Tval r a22 a3 a28 a4]
    · simp [Scell, Tcell]
  · unfold winCost
    rw [← hs, ← hL]
    omega

end Win

end NearCubicWires.WireExponent3_5.UnionMachine.EwRecs
