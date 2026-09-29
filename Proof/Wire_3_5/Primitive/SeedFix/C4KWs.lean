import Proof.Wire_3_5.Primitive.SeedFix.C4KWr

/-! # C4KW, part 18: stage B2's teardown and run

After the levels, the words `P`, `C` are overwritten by falses (`eraseF`), the numbers cleared, and the outer
terminator written: **`b2_core`**: from B2's entry, the output holds `outL (J+1) ++ [false]` (every level's cleared
weight doubly framed), the inputs kept, the words falses, every register `0`.

Paper quantity of the main type: the cleared weights' word `wtWord (wsOf MP)`, framed (P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.UnionMachine.EwLevel (twW twW_spec twOf twMax twOf_le twCost)
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_st_d apd_st_ne apd_sh_d apd_sh_ne wlist wlist_spec)

/-- **B2's teardown**: the words erased, the numbers cleared, the outer terminator. -/
def teardownW : WM 5 48 :=
  .seq (eraseF sP) (.seq (eraseF sC) (.seq (WM.clear (Vr 0)) (.seq (WM.clear (Vr 1)) (.seq (WM.clear rJ)
    (.seq (WM.clear rB) (.seq (WM.clear rt2) (.seq (WM.clear 27) (.seq (WM.clear rl) (wlist 0 [false])))))))))

/-- **B2's word program.** -/
def b2P : WM 5 48 := .seq setupW (.seq (.whr rL lBody) teardownW)

/-- The teardown's cost. -/
def tearCost (t s J B : ℕ) : ℕ :=
  (wdOf t s J * 9 + 1) + 1 + ((wdOf t s J * 9 + 1) + 1 + ((3 * t + 1) + 1 + ((3 * s + 1) + 1 + ((3 * J + 1) + 1 +
    ((3 * B + 1) + 1 + ((3 * (2 * t) + 1) + 1 + ((3 * wdOf t s J + 1) + 1 + ((3 * (J + 1) + 1) + 1 + 4 * 1))))))))

/-- B2's steps. -/
def b2Cost (t s J B : ℕ) : ℕ :=
  setupCost t s J B + 1 + (((J + 1) * (lCost (wdOf t s J) t s J + 2) + 1) + 1 + tearCost t s J B)

section Run
variable (σ0 : WState 5 48) (t J B s : ℕ) (hv0 : ∀ r, σ0.val r = 0)
include hv0

theorem outC_val (r : Fin 48) : (outC σ0 t J B s).val r =
    if r = rL then J + 1 else if r = 27 then wdOf t s J else if r = rt2 then 2 * t else if r = Vr 1 then s else
    if r = rB then B else if r = rJ then J else if r = Vr 0 then t else 0 := by
  simp only [outC, outB, outA, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, hv0]

theorem outC_st (i : Fin 6) : (outC σ0 t J B s).st i =
    if i = sC then frame (binary (wdOf t s J) 0) else if i = sP then frame (binary (wdOf t s J) 0) else σ0.st i := by
  simp only [outC, outB, outA, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]

theorem outC_sh (i : Fin 6) : (outC σ0 t J B s).sh i =
    if i = 3 then B else if i = 2 then J else if i = 1 then t else σ0.sh i := by
  simp only [outC, outB, outA, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]

theorem outC_Vz (i : Fin 20) (hi : 3 ≤ i.val) : (outC σ0 t J B s).val (Vr i) = 0 := by
  have := i.isLt
  rw [outC_val σ0 t J B s hv0]
  have e1 : Vr i ≠ rL := fun e => by have := congrArg Fin.val e; simp at this; omega
  have e2 : Vr i ≠ 27 := fun e => by have := congrArg Fin.val e; simp at this; omega
  have e3 : Vr i ≠ rt2 := fun e => by have := congrArg Fin.val e; simp at this; omega
  have e4 : Vr i ≠ Vr 1 := fun e => by have := congrArg Fin.val e; simp at this; omega
  have e5 : Vr i ≠ rB := fun e => by have := congrArg Fin.val e; simp at this; omega
  have e6 : Vr i ≠ rJ := fun e => by have := congrArg Fin.val e; simp at this; omega
  have e7 : Vr i ≠ Vr 0 := fun e => by have := congrArg Fin.val e; simp at this; omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6, if_neg e7]

variable (hsh0 : ∀ i, σ0.sh i = 0) (hs0 : σ0.st 0 = []) (hsP : σ0.st sP = []) (hsC : σ0.st sC = [])
include hsh0 hs0

theorem b2_in : RLin (outC σ0 t J B s) t s J :=
  ⟨⟨by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl, outC_Vz σ0 t J B s hv0,
    by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl,
    by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl,
    by rw [outC_val σ0 t J B s hv0]; rfl⟩,
    by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl,
    by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl⟩

theorem b2_rl0 : RL (outC σ0 t J B s) (wdOf t s J) t s J 0 (outC σ0 t J B s) :=
  ⟨by simp [outL], by rw [outC_sh σ0 t J B s hv0, outC_st σ0 t J B s hv0, hsh0]; simp (config := {decide := true}) [hs0],
    ⟨0, ⟨by rw [outC_st σ0 t J B s hv0]; rfl, by rw [outC_sh σ0 t J B s hv0, hsh0]; rfl⟩⟩, ⟨0, ⟨by rw [outC_st σ0 t J B s hv0]; rfl, by rw [outC_sh σ0 t J B s hv0, hsh0]; rfl⟩⟩,
    by rw [outC_val σ0 t J B s hv0]; rfl, by rw [outC_val σ0 t J B s hv0]; rfl,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- The teardown's registers end at `0`. -/
theorem tear_val (τ : WState 5 48) (x y : ℕ)
    (hτv : τ.val = fun r => if r = rl then J + 1 else if r = rL then 0 else (outC σ0 t J B s).val r) (r : Fin 48) :
    ((((((((((((τ).sets sP (List.replicate (2 * x + 1) false)).seth sP (2 * x)).sets sC (List.replicate (2 * y + 1) false)).seth sC (2 * y)).setv (Vr 0) 0).setv (Vr 1) 0).setv rJ 0).setv rB 0).setv rt2 0).setv 27 0).setv rl 0).val r = 0 := by
  simp only [WState.setv_val, WState.seth_val, WState.sets_val, hτv, Function.update_apply]
  rw [outC_val σ0 t J B s hv0]
  split_ifs <;> first | rfl | (exfalso; simp_all (config := {decide := true}))

/-- **The teardown's run** (from the levels' exit). -/
theorem tear_run (cp : ℕ) (τ : WState 5 48) (h : RL (outC σ0 t J B s) (wdOf t s J) t s J (J + 1) τ)
    (hcp : 2 * t + s + J + B + wdOf t s J + 2 ≤ cp) :
    ∃ τf : WState 5 48, WExec cp teardownW τ τf (tearCost t s J B) ∧ τf.cell = τ.cell ∧ (∀ r, τf.val r = 0) ∧
      τf.st 0 = τ.st 0 ++ [false] ∧ (∀ i : Fin 6, i ≠ 0 → i ≠ sP → i ≠ sC → τf.st i = τ.st i) ∧
      τf.st sP = List.replicate (2 * wdOf t s J + 1) false ∧ τf.st sC = List.replicate (2 * wdOf t s J + 1) false := by
  obtain ⟨x, hx⟩ := h.P
  obtain ⟨y, hy⟩ := h.C
  have hτv : τ.val = fun r => if r = rl then J + 1 else if r = rL then 0 else (outC σ0 t J B s).val r := by
    funext r
    by_cases h1 : r = rl
    · rw [if_pos h1, h1, h.lv]
    · by_cases h2 : r = rL
      · rw [if_neg h1, if_pos h2, h2, h.Lv]; omega
      · rw [if_neg h1, if_neg h2, h.vl r h1 h2]
  have ov : ∀ r, (outC σ0 t J B s).val r = _ := outC_val σ0 t J B s hv0
  have t1 := eraseF_spec cp sP (binary (wdOf t s J) x) τ hx.1 hx.2
  have t2 := eraseF_spec cp sC (binary (wdOf t s J) y) ((τ.sets sP (List.replicate (2 * (binary (wdOf t s J) x).length + 1) false)).seth sP (2 * (binary (wdOf t s J) x).length))
    (by simp only [WState.seth_st, WState.sets_st]; rw [Function.update_of_ne (by decide)]; exact hy.1)
    (by simp only [WState.seth_sh, WState.sets_sh]; rw [Function.update_of_ne (by decide)]; exact hy.2)
  set τ4 := ((((τ).sets sP (List.replicate (2 * (binary (wdOf t s J) x).length + 1) false)).seth sP (2 * (binary (wdOf t s J) x).length)).sets sC (List.replicate (2 * (binary (wdOf t s J) y).length + 1) false)).seth sC (2 * (binary (wdOf t s J) y).length) with hτ4
  have v4 : τ4.val = τ.val := rfl
  have t5 := wclear_spec cp (Vr 0) t τ4 (by rw [v4, hτv]; simp only; rw [ov]; rfl) (by rw [v4, hτv]; simp only; rw [ov]; simp (config := {decide := true}); omega)
  have t6 := wclear_spec cp (Vr 1) s (τ4.setv (Vr 0) 0) (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; rfl)
    (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; simp (config := {decide := true}); omega)
  have t7 := wclear_spec cp rJ J ((τ4.setv (Vr 0) 0).setv (Vr 1) 0) (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; rfl)
    (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; simp (config := {decide := true}); omega)
  have t8 := wclear_spec cp rB B (((τ4.setv (Vr 0) 0).setv (Vr 1) 0).setv rJ 0) (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; rfl)
    (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; simp (config := {decide := true}); omega)
  have t9 := wclear_spec cp rt2 (2 * t) ((((τ4.setv (Vr 0) 0).setv (Vr 1) 0).setv rJ 0).setv rB 0) (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; rfl)
    (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; simp (config := {decide := true}); omega)
  have t10 := wclear_spec cp 27 (wdOf t s J) (((((τ4.setv (Vr 0) 0).setv (Vr 1) 0).setv rJ 0).setv rB 0).setv rt2 0) (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; rfl)
    (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, hτv]; simp only; rw [ov]; simp (config := {decide := true}); omega)
  have t11 := wclear_spec cp rl (J + 1) ((((((τ4.setv (Vr 0) 0).setv (Vr 1) 0).setv rJ 0).setv rB 0).setv rt2 0).setv 27 0) (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, h.lv])
    (by simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), v4, h.lv]; omega)
  set τ11 := (((((((τ4.setv (Vr 0) 0).setv (Vr 1) 0).setv rJ 0).setv rB 0).setv rt2 0).setv 27 0).setv rl 0) with hτ11
  have hO : τ11.sh 0 = (τ11.st 0).length := by
    rw [hτ11, hτ4]; simp only [WState.setv_sh, WState.setv_st, WState.seth_sh, WState.sets_sh, WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact h.oh
  have t12 := wlist_spec cp (0 : Fin 6) [false] τ11 hO
  refine ⟨_, WExec.mono (WExec.seq t1 (WExec.seq t2 (WExec.seq t5 (WExec.seq t6 (WExec.seq t7 (WExec.seq t8 (WExec.seq t9
    (WExec.seq t10 (WExec.seq t11 t12))))))))) ?_, rfl, fun r => ?_, ?_, fun i h1 h2 h3 => ?_, ?_, ?_⟩
  · unfold tearCost; simp only [SignedSortKey.binary_length, List.length_singleton]; omega
  · show τ11.val r = 0
    exact tear_val σ0 t J B s hv0 hsh0 hs0 τ _ _ hτv r
  · rw [apd_st_d, hτ11, hτ4]; simp only [WState.setv_st, WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · rw [apd_st_ne _ _ _ h1, hτ11, hτ4]; simp only [WState.setv_st, WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne h3, Function.update_of_ne h2]
  · rw [apd_st_ne _ _ _ (by decide), hτ11, hτ4]; simp only [WState.setv_st, WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne (by decide), Function.update_self, SignedSortKey.binary_length]
  · rw [apd_st_ne _ _ _ (by decide), hτ11, hτ4]; simp only [WState.setv_st, WState.seth_st, WState.sets_st]
    rw [Function.update_self, SignedSortKey.binary_length]

end Run

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
