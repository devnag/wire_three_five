import Proof.Wire_3_5.Primitive.Writers.HashPops1

/-! # HASH setup (C), P2a part 2: the tracked state's updates and the segment copy

* the updates of `LS.w` under the word language's steps (`appendO_w`, `seth_Dg_w`, `setv_K_w`, …);
* `cpBit`, **`cpBit_spec`**; `onesCW`, **`ones_spec`**; `elemCW`, **`elem_spec`**; `segLoopW`, **`segLoop_spec`**;
  `segCW`, **`seg_spec`**: a digit population's segment `gis.flatMap elemW ++ [false]` copied from `Dg` to `O`.

Paper quantity of the main type: the words of the HASH call's populations (`popRec`, P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

section Upd
variable {ns nr : ℕ} (L : PL ns nr) (h : L.Ok) (σB : WState ns nr) (t : LS)
include h

theorem appendO_w (u : List Bool) : appendO (t.w L σB) L.O L.OP u = ({ t with out := t.out ++ u }).w L σB := by
  apply WState.eq
  · funext s
    simp only [appendO_sh, LS.w, Function.update_apply]
    by_cases hs : s = L.O
    · subst hs; simp
    · simp [hs]
  · funext s
    simp only [appendO_st, LS.w, Function.update_apply]
    by_cases hs : s = L.O
    · subst hs; simp
    · simp [hs]
  · funext r
    simp only [appendO_val, LS.w, Function.update_apply]
    by_cases hr : r = L.OP
    · subst hr; simp
    · simp [hr]
  · rfl

theorem seth_Dg_w (x : ℕ) : (t.w L σB).seth L.Dg x = ({ t with dh := x }).w L σB := by
  apply WState.eq
  · funext s
    simp only [WState.seth_sh, LS.w, Function.update_apply]
    by_cases hs : s = L.Dg
    · subst hs; simp [(O_Dg h).symm]
    · simp [hs]
  · rfl
  · rfl
  · rfl

theorem sets_Dg_w (l : List Bool) : (t.w L σB).sets L.Dg l = ({ t with dg := l }).w L σB := by
  apply WState.eq
  · rfl
  · funext s
    simp only [WState.sets_st, LS.w, Function.update_apply]
    by_cases hs : s = L.Dg
    · subst hs; simp [(O_Dg h).symm]
    · simp [hs]
  · rfl
  · rfl

theorem setv_K_w (x : ℕ) : (t.w L σB).setv L.K x = ({ t with k := x }).w L σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, LS.w, Function.update_apply]
    by_cases hr : r = L.K
    · subst hr; simp [(neOP_K L h).symm]
    · simp [hr]
  · rfl

theorem setv_DL_w (x : ℕ) : (t.w L σB).setv L.DL x = ({ t with dl := x }).w L σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, LS.w, Function.update_apply]
    by_cases hr : r = L.DL
    · subst hr; simp [(neOP_DL L h).symm, (neK_DL L h).symm]
    · simp [hr]
  · rfl

theorem setv_DC_w (x : ℕ) : (t.w L σB).setv L.DC x = ({ t with dc := x }).w L σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, LS.w, Function.update_apply]
    by_cases hr : r = L.DC
    · subst hr; simp [(neOP_DC L h).symm, (neK_DC L h).symm, (neDL_DC L h).symm]
    · simp [hr]
  · rfl

theorem setv_GR_w (x : ℕ) : (t.w L σB).setv L.GR x = ({ t with gr := x }).w L σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, LS.w, Function.update_apply]
    by_cases hr : r = L.GR
    · subst hr; simp [(neOP_GR L h).symm, (neK_GR L h).symm, (neDL_GR L h).symm, (neDC_GR L h).symm]
    · simp [hr]
  · rfl

theorem setv_1_w (x : ℕ) : (t.w L σB).setv (L.R 1) x = ({ t with gi := x }).w L σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, LS.w, Function.update_apply]
    by_cases hr : r = L.R 1
    · subst hr
      simp [(neOP_1 L h).symm, (neK_1 L h).symm, (neDL_1 L h).symm, (neDC_1 L h).symm, (neGR_1 L h).symm]
    · simp [hr]
  · rfl

theorem setv_2_w (x : ℕ) : (t.w L σB).setv (L.R 2) x = ({ t with p := x }).w L σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, LS.w, Function.update_apply]
    by_cases hr : r = L.R 2
    · subst hr
      simp [(neOP_2 L h).symm, (neK_2 L h).symm, (neDL_2 L h).symm, (neDC_2 L h).symm, (neGR_2 L h).symm,
        (ne1_2 L h).symm]
    · simp [hr]
  · rfl

theorem seth_PR_setv_PH_w (x : ℕ) : ((t.w L σB).seth L.PR x).setv L.PH x = ({ t with ph := x }).w L σB := by
  apply WState.eq
  · funext s
    simp only [WState.setv_sh, WState.seth_sh, LS.w, Function.update_apply]
    by_cases hs : s = L.PR
    · subst hs; simp [(O_PR h).symm, (Dg_PR h).symm]
    · simp [hs]
  · rfl
  · funext r
    simp only [WState.setv_val, WState.seth_val, LS.w, Function.update_apply]
    by_cases hr : r = L.PH
    · subst hr
      simp [(neOP_PH L h).symm, (neK_PH L h).symm, (neDL_PH L h).symm, (neDC_PH L h).symm, (neGR_PH L h).symm,
        (ne1_PH L h).symm, (ne2_PH L h).symm]
    · simp [hr]
  · rfl

theorem setv_PH_seth_PR_w (x : ℕ) : ((t.w L σB).setv L.PH x).seth L.PR x = ({ t with ph := x }).w L σB := by
  rw [← seth_PR_setv_PH_w L h σB t x]
  rfl

end Upd

/-! ## Reading a tape -/

theorem rd_app (A B : List Bool) (i : ℕ) : readTapeBit (A ++ B) (A.length + i) = readTapeBit B i := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem rd_ones (q i : ℕ) (V : List Bool) (hi : i < q) : readTapeBit (List.replicate q true ++ V) i = true := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < (List.replicate q true).length by
    simpa using hi), hi]

theorem rd_zero (q : ℕ) (V : List Bool) : readTapeBit (List.replicate q true ++ false :: V) q = false := by
  have e := rd_app (List.replicate q true) (false :: V) 0
  rw [List.length_replicate, Nat.add_zero] at e
  rw [e]
  rfl

/-! ## The bit copies -/

section Copy
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

/-- One bit `b` copied: appended to `O`, `Dg`'s head and `K` advanced. -/
def cpBit (b : Bool) : WM ns nr := .seq (emitC L.O L.OP b) (.seq (.fwd L.Dg) (.inc L.K))

theorem cpBit_spec (b : Bool) (t : LS) (h1 : t.out.length < cap) (h2 : t.k < cap) :
    WExec cap (cpBit L b) (t.w L σB) ({ t with out := t.out ++ [b], dh := t.dh + 1, k := t.k + 1 }.w L σB) 13 := by
  have e1 := emitC_spec cap L.O L.OP b (t.w L σB) (by rw [w_sh_O L h, w_st_O L h]) (by rw [w_OP L h]; exact h1)
  rw [show (((t.w L σB).sets L.O ((t.w L σB).st L.O ++ [b])).seth L.O ((t.w L σB).sh L.O + 1)).setv L.OP
      ((t.w L σB).val L.OP + 1) = appendO (t.w L σB) L.O L.OP [b] from rfl, appendO_w L h] at e1
  have e2 := WExec.fwd (cap := cap) L.Dg ({ t with out := t.out ++ [b] }.w L σB)
  rw [w_sh_Dg L h, seth_Dg_w L h] at e2
  have e3 := WExec.inc (cap := cap) L.K ({ t with out := t.out ++ [b], dh := t.dh + 1 }.w L σB)
    (by rw [w_K L h]; exact h2)
  rw [w_K L h, setv_K_w L h] at e3
  exact WExec.seq e1 (WExec.seq e2 e3)

/-- The ones of an element, copied. -/
def onesCW : WM ns nr := .whs L.Dg (cpBit L true)

theorem ones_spec : ∀ (m : ℕ) (t : LS), (∀ i < m, readTapeBit t.dg (t.dh + i) = true) →
    readTapeBit t.dg (t.dh + m) = false → t.out.length + m ≤ cap → t.k + m ≤ cap →
    WExec cap (onesCW L) (t.w L σB)
      ({ t with out := t.out ++ List.replicate m true, dh := t.dh + m, k := t.k + m }.w L σB) (15 * m + 1)
  | 0, t, _, h0, _, _ => by
    have e := WExec.whsF (cap := cap) (P := cpBit L true) (i := L.Dg) (σ := t.w L σB)
      (by unfold wbit; rw [w_st_Dg L h, w_sh_Dg L h]; simpa using h0)
    have ht : { t with out := t.out ++ List.replicate 0 true, dh := t.dh + 0, k := t.k + 0 } = t := by
      cases t; simp
    rw [ht]
    exact e
  | m + 1, t, hT, hF, hc1, hc2 => by
    have e1 := cpBit_spec cap L h σB true t (by omega) (by omega)
    have ih := ones_spec m { t with out := t.out ++ [true], dh := t.dh + 1, k := t.k + 1 }
      (fun i hi => by have := hT (i + 1) (by omega); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      (by have := hF; simpa [Nat.add_assoc, Nat.add_comm 1 m] using this)
      (by simp; omega) (by simp; omega)
    have e := WExec.whsT (cap := cap) (i := L.Dg)
      (by unfold wbit; rw [w_st_Dg L h, w_sh_Dg L h]; simpa using hT 0 (by omega)) e1 ih
    refine WExec.cast cap e ?_ (by omega)
    congr 1
    cases t
    simp only [LS.mk.injEq, List.append_assoc, List.singleton_append, List.replicate_succ, true_and, and_true]
    omega

end Copy

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
