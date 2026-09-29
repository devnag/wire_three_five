import Proof.Wire_3_5.Primitive.SeedFix.C4KWp

/-! # C4KW, part 16: stage B2's level body (one cleared weight, emitted)

For the level `λ` (register `rl`): `P := 1`, the levels `j < λ`, skip `λ`, the levels `λ < j < J`, so
`P = vOf λ = Π_{j<λ} W_j^{2t} · Π_{λ<j<J} W_j^{2t}`, then `Nat.bits P` doubly framed onto the output
(**`l_step`**, invariant `RL`: after `λ` levels the output holds `Σ_{λ'<λ} prs (frame (Nat.bits (vOf λ')))`).

Paper quantity of the main type: the cleared weights `W_λ` of the Hb printer's stream `WT` (P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.UnionMachine.EwLevel (twW twW_spec twOf twMax twOf_le twCost)
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_st_d apd_st_ne apd_sh_d apd_sh_ne)

/-! ## Values -/

theorem fac_le (t s j0 n : ℕ) : fac t s j0 n ≤ twMax t s ^ (2 * t * n) := by
  unfold fac
  calc ∏ i ∈ Finset.range n, twOf t s (j0 + i) ^ (2 * t) ≤ ∏ _i ∈ Finset.range n, twMax t s ^ (2 * t) :=
        Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (twOf_le t s _) _
    _ = twMax t s ^ (2 * t * n) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

/-- The level `λ`'s cleared weight, as the machine forms it. -/
def vOf (t s J l : ℕ) : ℕ := fac t s 0 l * fac t s (l + 1) (J - (l + 1))

theorem vOf_le (t s J l : ℕ) (hl : l ≤ J) : vOf t s J l ≤ twMax t s ^ (2 * t * J) := by
  have hm : 1 ≤ twMax t s := by unfold twMax; omega
  unfold vOf
  calc fac t s 0 l * fac t s (l + 1) (J - (l + 1)) ≤ twMax t s ^ (2 * t * l) * twMax t s ^ (2 * t * (J - (l + 1))) :=
        Nat.mul_le_mul (fac_le _ _ _ _) (fac_le _ _ _ _)
    _ = twMax t s ^ (2 * t * (l + (J - (l + 1)))) := by rw [← pow_add, Nat.mul_add]
    _ ≤ twMax t s ^ (2 * t * J) := Nat.pow_le_pow_right hm (Nat.mul_le_mul_left _ (by omega))

theorem facA_le (t s J l : ℕ) (hl : l ≤ J) : fac t s 0 l ≤ twMax t s ^ (2 * t * J) := by
  have hm : 1 ≤ twMax t s := by unfold twMax; omega
  exact (fac_le _ _ _ _).trans (Nat.pow_le_pow_right hm (Nat.mul_le_mul_left _ hl))

/-! ## One level -/

abbrev E0 : List Bool := [true, true, true, false]
abbrev E1 : List Bool := [true, true, true, true]
abbrev TM : List Bool := [true, false]

/-- **One level `λ`**: its cleared weight on `P`, emitted doubly framed. -/
def lBody : WM 5 48 :=
  .seq (.dec rL) (.seq (UnionMachine.RegRat.oneB sP sC rF rR) (.seq (UnionMachine.RegRat.copyB sC sP rF rR)
    (.seq (UnionMachine.BinW.dupR rl rE rT) (.seq rngW (.seq (.inc (Vr 2)) (.seq (UnionMachine.BinW.dupR rJ rE rT)
    (.seq (UnionMachine.EwKit.subR (Vr 2) rE rT rU) (.seq rngW (.seq (WM.clear (Vr 2))
    (.seq (emitB 0 sP rz rc E0 E1 TM) (.inc rl)))))))))))

/-- The output after `λ` levels. -/
def outL (t s J l : ℕ) : List Bool := (List.range l).flatMap fun l' => prs (frame (Nat.bits (vOf t s J l')))

/-- **The levels' invariant** after `λ` levels. -/
structure RL (σ : WState 5 48) (wd t s J l : ℕ) (τ : WState 5 48) : Prop where
  O : τ.st 0 = σ.st 0 ++ outL t s J l
  oh : τ.sh 0 = (τ.st 0).length
  P : ∃ x, NumOn τ sP wd x
  C : ∃ x, NumOn τ sC wd x
  lv : τ.val rl = l
  Lv : τ.val rL = J + 1 - l
  vl : ∀ r, r ≠ rl → r ≠ rL → τ.val r = σ.val r
  st : ∀ i : Fin 6, i ≠ 0 → i ≠ sP → i ≠ sC → τ.st i = σ.st i
  sh : ∀ i : Fin 6, i ≠ 0 → τ.sh i = σ.sh i
  cl : τ.cell = σ.cell

/-- The levels' entry conditions. -/
structure RLin (σ : WState 5 48) (t s J : ℕ) : Prop where
  j : RJin σ t s
  v2 : σ.val (Vr 2) = 0
  jj : σ.val rJ = J
  e : σ.val rE = 0
  u : σ.val rU = 0
  z : σ.val rz = 0

/-- The level body's cost. -/
def lCost (wd t s J : ℕ) : ℕ := 8 * (J + 2) * (jCost wd t s J + 30) + 200 * wd + emitCostB wd + 300

theorem fac_zero (t s j0 : ℕ) : fac t s j0 0 = 1 := by simp [fac]

theorem outL_succ (t s J l : ℕ) : outL t s J (l + 1) = outL t s J l ++ prs (frame (Nat.bits (vOf t s J l))) := by
  unfold outL; rw [List.range_succ, List.flatMap_append]; simp

/-- **One level.** -/
theorem l_step (cap : ℕ) (σ : WState 5 48) (wd t s J l : ℕ) (hin : RLin σ t s J) (hl : l < J + 1)
    (hW : twMax t s ^ (2 * t * J) < 2 ^ wd) (hwd : 1 ≤ wd)
    (hcap : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 2 * wd + 2 * t + twMax t s + 10 ≤ cap)
    (τ : WState 5 48) (h : RL σ wd t s J l τ) :
    ∃ τ' : WState 5 48, ∃ c, WExec cap lBody τ τ' c ∧ c ≤ lCost wd t s J ∧ RL σ wd t s J (l + 1) τ' := by
  obtain ⟨x, hx⟩ := h.P
  obtain ⟨y, hy⟩ := h.C
  have g1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have hcap' : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 2 * wd + 2 * t + twMax t s + 1 ≤ cap := by omega
  -- 1. the level counter
  have t1 := WExec.dec (cap := cap) rL τ (by rw [h.Lv]; omega)
  set τ1 := τ.setv rL (τ.val rL - 1) with hτ1
  have v1 : ∀ r, r ≠ rL → r ≠ rl → τ1.val r = σ.val r := fun r h1 h2 => by
    rw [hτ1]; simp only [WState.setv_val]; rw [Function.update_of_ne h1]; exact h.vl r h2 h1
  -- 2. `P := 1`, 3. `C := 1`
  have t2 := UnionMachine.RegRat.oneB_spec cap wd (A := sP) (B := sC) (F := rF) (R := rR) (by decide) (by decide)
    τ1 x y hx hy (by rw [v1 _ (by decide) (by decide), hin.j.f]) (by rw [v1 _ (by decide) (by decide), hin.j.r])
    hwd (by omega)
  set τ2 := τ1.sets sP (frame (binary wd 1)) with hτ2
  have hP2 : NumOn τ2 sP wd 1 := numOn_sets τ1 sP wd 1 hx.2
  have hC2 : NumOn τ2 sC wd y := numOn_sets_ne _ hy (by decide)
  have t3 := UnionMachine.RegRat.copyB_spec cap wd (A := sC) (B := sP) (F := rF) (R := rR) (by decide) (by decide)
    τ2 y 1 hC2 hP2 (by rw [hτ2]; exact (v1 _ (by decide) (by decide)).trans hin.j.f)
    (by rw [hτ2]; exact (v1 _ (by decide) (by decide)).trans hin.j.r) (by omega)
  set τ3 := τ2.sets sC (frame (binary wd 1)) with hτ3
  -- 4. `rE := λ`
  have t4 := UnionMachine.BinW.dupR_spec cap rl rE rT (by decide) (by decide) (by decide) τ3 l
    (by rw [hτ3, hτ2, hτ1]; simp only [WState.sets_val, WState.setv_val]; rw [Function.update_of_ne (by decide), h.lv])
    (by rw [hτ3, hτ2]; exact (v1 _ (by decide) (by decide)).trans hin.e)
    (by rw [hτ3, hτ2]; exact (v1 _ (by decide) (by decide)).trans hin.j.tt) (by omega)
  set τ4 := τ3.setv rE l with hτ4
  have v4 : ∀ r, r ≠ rE → r ≠ rL → r ≠ rl → τ4.val r = σ.val r := fun r h1 h2 h3 => by
    rw [hτ4]; simp only [WState.setv_val]; rw [Function.update_of_ne h1, hτ3, hτ2]; exact v1 r h2 h3
  have in4 : RJin τ4 t s := ⟨(v4 _ (by decide) (by decide) (by decide)).trans hin.j.t0,
    (v4 _ (by decide) (by decide) (by decide)).trans hin.j.s1,
    fun i hi => (v4 _ (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)).trans (hin.j.z i hi),
    (v4 _ (by decide) (by decide) (by decide)).trans hin.j.f, (v4 _ (by decide) (by decide) (by decide)).trans hin.j.r,
    (v4 _ (by decide) (by decide) (by decide)).trans hin.j.w, (v4 _ (by decide) (by decide) (by decide)).trans hin.j.c,
    (v4 _ (by decide) (by decide) (by decide)).trans hin.j.tt, (v4 _ (by decide) (by decide) (by decide)).trans hin.j.k,
    (v4 _ (by decide) (by decide) (by decide)).trans hin.j.m⟩
  -- 5. the levels below `λ`
  have r0 : RJ τ4 wd t s 0 l 1 0 τ4 := ⟨by rw [fac_zero]; exact numOn_sets_ne (frame (binary wd 1)) hP2 (by decide : sP ≠ sC),
    by rw [fac_zero]; exact numOn_sets τ2 sC wd 1 hC2.2,
    by rw [v4 _ (by decide) (by decide) (by decide), hin.v2], by rw [hτ4]; simp,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl⟩
  have hA : 1 * fac t s 0 l < 2 ^ wd := by rw [Nat.one_mul]; exact lt_of_le_of_lt (facA_le t s J l (by omega)) hW
  obtain ⟨τ5, t5, r5⟩ := rng_loop cap τ4 wd t s J 0 l 1 in4 (by omega) hA hcap' l 0 τ4 (by omega) r0
  -- 6. skip `λ`, 7. 8. `rE := J − (λ + 1)`
  have t6 := WExec.inc (cap := cap) (Vr 2) τ5 (by rw [r5.j]; omega)
  set τ6 := τ5.setv (Vr 2) (τ5.val (Vr 2) + 1) with hτ6
  have v6 : ∀ r, r ≠ Vr 2 → r ≠ rE → r ≠ rL → r ≠ rl → τ6.val r = σ.val r := fun r h1 h2 h3 h4 => by
    rw [hτ6]; simp only [WState.setv_val]; rw [Function.update_of_ne h1, r5.vl r h1 h2]; exact v4 r h2 h3 h4
  have t7 := UnionMachine.BinW.dupR_spec cap rJ rE rT (by decide) (by decide) (by decide) τ6 J
    ((v6 _ (by decide) (by decide) (by decide) (by decide)).trans hin.jj)
    (by rw [hτ6]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), r5.e]; omega)
    ((v6 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.tt) (by omega)
  set τ7 := τ6.setv rE J with hτ7
  have h72 : τ7.val (Vr 2) = l + 1 := by
    rw [hτ7, hτ6]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_self, r5.j]
    omega
  have t8 := UnionMachine.EwKit.subR_spec cap (Vr 2) rE rT rU (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) τ7 (l + 1) h72
    (by rw [hτ7]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)];
        exact (v6 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.tt)
    (by rw [hτ7]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)];
        exact (v6 _ (by decide) (by decide) (by decide) (by decide)).trans hin.u)
    (by omega) (by rw [hτ7]; simp only [WState.setv_val, Function.update_self]; omega)
  set τ8 := τ7.setv rE (τ7.val rE - (l + 1)) with hτ8
  have h8E : τ8.val rE = J - (l + 1) := by
    rw [hτ8]; simp only [WState.setv_val, Function.update_self]; rw [hτ7]; simp
  have v8 : ∀ r, r ≠ Vr 2 → r ≠ rE → r ≠ rL → r ≠ rl → τ8.val r = σ.val r := fun r h1 h2 h3 h4 => by
    rw [hτ8, hτ7]; simp only [WState.setv_val]; rw [Function.update_of_ne h2, Function.update_of_ne h2]
    exact v6 r h1 h2 h3 h4
  have in8 : RJin τ8 t s := ⟨(v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.t0,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.s1,
    fun i hi => (v8 _ (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)
      (by intro e; have := congrArg Fin.val e; simp at this; omega)).trans (hin.j.z i hi),
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.f,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.r,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.w,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.c,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.tt,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.k,
    (v8 _ (by decide) (by decide) (by decide) (by decide)).trans hin.j.m⟩
  -- 9. the levels above `λ`
  have r8j : τ8.val (Vr 2) = l + 1 + 0 := by
    rw [hτ8]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), h72]
  have r8 : RJ τ8 wd t s (l + 1) (J - (l + 1)) (1 * fac t s 0 l) 0 τ8 := ⟨by rw [fac_zero, Nat.mul_one]; exact r5.P,
    by rw [fac_zero, Nat.mul_one]; exact r5.C, r8j, by rw [h8E]; rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, rfl⟩
  have hv : vOf t s J l < 2 ^ wd := lt_of_le_of_lt (vOf_le t s J l (by omega)) hW
  have hB : 1 * fac t s 0 l * fac t s (l + 1) (J - (l + 1)) < 2 ^ wd := by rw [Nat.one_mul]; exact hv
  obtain ⟨τ9, t9, r9⟩ := rng_loop cap τ8 wd t s J (l + 1) (J - (l + 1)) (1 * fac t s 0 l) in8 (by omega) hB hcap'
    (J - (l + 1)) 0 τ8 (by omega) r8
  -- 10. clear the level register
  have t10 := wclear_spec cap (Vr 2) (l + 1 + (J - (l + 1))) τ9 r9.j (by rw [r9.j]; omega)
  set τ10 := τ9.setv (Vr 2) 0 with hτ10
  have eV : 1 * fac t s 0 l * fac t s (l + 1) (J - (l + 1)) = vOf t s J l := by rw [Nat.one_mul]; rfl
  have hP10 : τ10.st sP = frame (binary wd (vOf t s J l)) := by rw [hτ10, ← eV]; exact r9.P.1
  have hPh10 : τ10.sh sP = 0 := r9.P.2
  have st10 : ∀ i : Fin 6, i ≠ sP → i ≠ sC → τ10.st i = τ.st i := fun i h1 h2 => by
    rw [hτ10]; simp only [WState.setv_st]; rw [r9.st i h1 h2, hτ8, hτ7, hτ6]; simp only [WState.setv_st]
    rw [r5.st i h1 h2, hτ4, hτ3, hτ2, hτ1]; simp only [WState.setv_st, WState.sets_st]
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have sh10 : ∀ i : Fin 6, i ≠ sP → i ≠ sC → τ10.sh i = τ.sh i := fun i h1 h2 => by
    rw [hτ10]; simp only [WState.setv_sh]; rw [r9.sh i h1 h2, hτ8, hτ7, hτ6]; simp only [WState.setv_sh]
    rw [r5.sh i h1 h2, hτ4, hτ3, hτ2, hτ1]; rfl
  have hO10 : τ10.sh 0 = (τ10.st 0).length := by
    rw [sh10 0 (by decide) (by decide), st10 0 (by decide) (by decide)]; exact h.oh
  have v10 : ∀ r, r ≠ rE → r ≠ rL → r ≠ rl → τ10.val r = σ.val r := fun r h1 h2 h3 => by
    by_cases h4 : r = Vr 2
    · rw [h4, hτ10]; simp only [WState.setv_val, Function.update_self]; exact hin.v2.symm
    · rw [hτ10]; simp only [WState.setv_val]; rw [Function.update_of_ne h4, r9.vl r h4 h1]; exact v8 r h4 h1 h2 h3
  -- 11. the level's cleared weight, doubly framed
  have t11 := emitB_spec cap (O := 0) (P := sP) (z := rz) (q := rc) (by decide) (by decide) E0 E1 TM (by decide)
    (by decide) (by decide) τ10 wd (vOf t s J l) hP10 hPh10 hO10
    ((v10 _ (by decide) (by decide) (by decide)).trans hin.z) ((v10 _ (by decide) (by decide) (by decide)).trans hin.j.c)
    hv (by omega)
  -- 12. the next level
  have h10l : τ10.val rl = l := by
    rw [hτ10]; simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), r9.vl _ (by decide) (by decide), hτ8, hτ7, hτ6]
    simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      r5.vl _ (by decide) (by decide), hτ4, hτ3, hτ2, hτ1]
    simp only [WState.setv_val, WState.sets_val]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h.lv]
  have h10L : τ10.val rL = J + 1 - l - 1 := by
    rw [hτ10]; simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), r9.vl _ (by decide) (by decide), hτ8, hτ7, hτ6]
    simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      r5.vl _ (by decide) (by decide), hτ4, hτ3, hτ2, hτ1]
    simp only [WState.setv_val, WState.sets_val]
    rw [Function.update_of_ne (by decide), Function.update_self, h.Lv]
  have t12 := WExec.inc (cap := cap) rl (apd τ10 0 (cw E0 E1 (Nat.bits (vOf t s J l)) ++ TM))
    (by simp only [apd_val]; rw [h10l]; omega)
  refine ⟨_, _, WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 (WExec.seq t5 (WExec.seq t6 (WExec.seq t7
    (WExec.seq t8 (WExec.seq t9 (WExec.seq t10 (WExec.seq t11 t12)))))))))), ?_, ?_⟩
  · have hj1 : l * (jCost wd t s J + 2) ≤ (J + 1) * (jCost wd t s J + 2) := Nat.mul_le_mul_right _ (by omega)
    have hj2 : (J - (l + 1)) * (jCost wd t s J + 2) ≤ (J + 1) * (jCost wd t s J + 2) := Nat.mul_le_mul_right _ (by omega)
    have hj3 : (J + 1) * (jCost wd t s J + 2) ≤ 4 * (J + 2) * (jCost wd t s J + 30) := by nlinarith
    unfold lCost
    nlinarith
  · have hE0 : prs (frame (Nat.bits (vOf t s J l))) = cw E0 E1 (Nat.bits (vOf t s J l)) ++ TM := frame2_cw _
    refine ⟨?_, ?_, ⟨vOf t s J l, ?_⟩, ⟨vOf t s J l, ?_⟩, ?_, ?_, fun r h1 h2 => ?_, fun i h1 h2 h3 => ?_,
      fun i h1 => ?_, ?_⟩
    · simp only [WState.setv_st]; rw [apd_st_d, st10 0 (by decide) (by decide), h.O, outL_succ, hE0,
        List.append_assoc]
    · simp only [WState.setv_st, WState.setv_sh]; rw [apd_st_d, apd_sh_d]; simp only [List.length_append]
    · refine ⟨?_, ?_⟩
      · simp only [WState.setv_st]; rw [apd_st_ne _ _ _ (by decide)]; exact hP10
      · simp only [WState.setv_sh]; rw [apd_sh_ne _ _ _ (by decide)]; exact hPh10
    · refine ⟨?_, ?_⟩
      · simp only [WState.setv_st]; rw [apd_st_ne _ _ _ (by decide)]; rw [hτ10, ← eV]; exact r9.C.1
      · simp only [WState.setv_sh]; rw [apd_sh_ne _ _ _ (by decide)]; exact r9.C.2
    · simp [h10l]
    · simp only [WState.setv_val, apd_val]; rw [Function.update_of_ne (by decide), h10L]; omega
    · simp only [WState.setv_val, apd_val]; rw [Function.update_of_ne h1]
      by_cases hE : r = rE
      · rw [hE, hτ10]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), r9.e, hin.e]; simp
      · exact v10 r hE h2 h1
    · simp only [WState.setv_st]; rw [apd_st_ne _ _ _ h1, st10 i h2 h3]; exact h.st i h1 h2 h3
    · simp only [WState.setv_sh]; rw [apd_sh_ne _ _ _ h1]
      by_cases hiP : i = sP
      · rw [hiP, hPh10, ← hx.2, h.sh sP (by decide)]
      · by_cases hiC : i = sC
        · rw [hiC]; show τ9.sh sC = σ.sh sC; rw [r9.C.2, ← hy.2, h.sh sC (by decide)]
        · rw [sh10 i hiP hiC]; exact h.sh i h1
    · simp only [WState.setv_cell, apd_cell]; rw [hτ10]; simp only [WState.setv_cell]; rw [r9.cl, hτ8, hτ7, hτ6]
      simp only [WState.setv_cell]; rw [r5.cl]; exact h.cl

/-- **The levels.** -/
theorem l_loop (cap : ℕ) (σ : WState 5 48) (wd t s J : ℕ) (hin : RLin σ t s J)
    (hW : twMax t s ^ (2 * t * J) < 2 ^ wd) (hwd : 1 ≤ wd)
    (hcap : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 2 * wd + 2 * t + twMax t s + 10 ≤ cap) :
    ∀ (m l : ℕ) (τ : WState 5 48), l + m = J + 1 → RL σ wd t s J l τ →
      ∃ τ' : WState 5 48, WExec cap (.whr rL lBody) τ τ' (m * (lCost wd t s J + 2) + 1) ∧ RL σ wd t s J (J + 1) τ'
  | 0, l, τ, hlm, h => by
    have hl : l = J + 1 := by omega
    subst hl
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [h.Lv]; omega)) (by omega), h⟩
  | m + 1, l, τ, hlm, h => by
    obtain ⟨τ1, c, t1, hc, h1⟩ := l_step cap σ wd t s J l hin (by omega) hW hwd hcap τ h
    obtain ⟨τ2, t2, h2⟩ := l_loop cap σ wd t s J hin hW hwd hcap m (l + 1) τ1 (by omega) h1
    refine ⟨τ2, WExec.mono (WExec.whrT (by rw [h.Lv]; omega) t1 t2) ?_, h2⟩
    rw [Nat.add_mul, Nat.one_mul]; omega

/-! ## The machine's weights are the cleared weights -/

theorem twOf_W (MP : Filters.MajorantParams) (j : ℕ) :
    twOf MP.t (Nat.sqrt (MP.t * MP.Bstar)) j = MP.W j := rfl

theorem vOf_eq (MP : Filters.MajorantParams) (l : ℕ) (hl : l ≤ MP.J) :
    vOf MP.t (Nat.sqrt (MP.t * MP.Bstar)) MP.J l = if l < MP.J then SeedFix.clearW MP l else SeedFix.prodW MP := by
  set f : ℕ → ℕ := fun j => MP.W j ^ (2 * MP.t) with hf
  have hA : fac MP.t (Nat.sqrt (MP.t * MP.Bstar)) 0 l = ∏ j ∈ Finset.range l, f j := by
    unfold fac; simp [hf, twOf_W]
  have hB : fac MP.t (Nat.sqrt (MP.t * MP.Bstar)) (l + 1) (MP.J - (l + 1)) = ∏ j ∈ Finset.Ico (l + 1) MP.J, f j := by
    unfold fac; rw [Finset.prod_Ico_eq_prod_range]; rfl
  unfold vOf
  rw [hA, hB]
  by_cases h : l < MP.J
  · rw [if_pos h]
    have hp := SeedFix.prodW_eq MP l h
    have h1 : SeedFix.prodW MP = f l * ((∏ j ∈ Finset.range l, f j) * ∏ j ∈ Finset.Ico (l + 1) MP.J, f j) := by
      unfold SeedFix.prodW
      rw [← Finset.prod_range_mul_prod_Ico f (le_of_lt h), Finset.prod_eq_prod_Ico_succ_bot h]
      ring
    have hpos : 0 < f l := pow_pos (by have := MP.W_ge l; omega) _
    rw [h1] at hp
    have hp2 : f l * ((∏ j ∈ Finset.range l, f j) * ∏ j ∈ Finset.Ico (l + 1) MP.J, f j) =
        f l * SeedFix.clearW MP l := hp
    exact Nat.eq_of_mul_eq_mul_left hpos hp2
  · rw [if_neg h]
    have hJ : l = MP.J := by omega
    subst hJ
    rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty, Nat.mul_one]
    rfl

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
