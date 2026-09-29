import Proof.Wire_3_5.FinalPass.SdEv

/-! # S4 (the seeds phase), part 6: the per-point step (P3:3044-3048, 3170-3178)

"At each column, evaluate the reported lookup at these `Q` pairs" (P3:3046-3048): at a sampled point `(c, u, v)` and
filter seed `e`, the numerator gains `M(e,x)·Σ R̂`. **`ptStep E`**: the carriers' factors into `rM 0`, `rM 1`
(`maskAll`); when both are `1`, the point's evaluator (`evalD E`) then the adder (`addA`); the two bits cleared.
**`ptStep_spec`**: from the point's state (`MaskCom`, `CarOK`, the bits and the accumulator `0`, the numerator
`frame (binary W x)`, the evaluators' scratch blank) and the evaluator's run at value `V` from any state agreeing off
the mask's streams (`hev`), the numerator becomes `frame (binary W (x + [carF 0 ∧ carF 1]·V))`; every register, head
and the cell as at entry; every stream but the numerator, the carriers' accumulators and corner words and the
evaluators' scratch as at entry; the scratch blank; `MaskCom`, `CarOK` again.

Paper quantity of the main type: the per-point term `M(e,x)·Σ R̂` added to the numerator (`ptThr`, `ptSym`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Lay
variable {nw nn nsc nrs : ℕ}

/-- Clear a bit register. -/
def clr (r : Fin (bnr nn nrs)) : BP nw nn nsc nrs := .ifr r (.dec r) .skip

theorem clr_spec (cap : ℕ) (r : Fin (bnr nn nrs)) (ω : BS nw nn nsc nrs) (h : ω.val r ≤ 1) (hc : 1 ≤ cap) :
    WExec cap (clr r) ω (ω.setv r 0) 2 := by
  by_cases h0 : ω.val r = 0
  · have e : ω.setv r 0 = ω := by rw [← h0, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.ifrF h0 (WExec.skip ω)) (by omega)
  · have e := WExec.dec (cap := cap) r ω (by omega)
    rw [show ω.val r - 1 = 0 by omega] at e
    exact WExec.ifrT h0 e

/-- The two bits cleared. -/
def clearM : BP nw nn nsc nrs := .seq (clr (rM 0)) (clr (rM 1))

theorem clearM_spec (cap : ℕ) (ω : BS nw nn nsc nrs) (h0 : ω.val (rM 0) ≤ 1) (h1 : ω.val (rM 1) ≤ 1)
    (hc : 1 ≤ cap) :
    WExec cap clearM ω ((ω.setv (rM 0) 0).setv (rM 1) 0) 5 := by
  have hne : (rM 1 : Fin (bnr nn nrs)) ≠ rM 0 := fun h => by
    have := congrArg Fin.val h
    simp [rM, brg] at this
  have e1 := clr_spec cap (rM 0) ω h0 hc
  have e2 := clr_spec cap (rM 1) (ω.setv (rM 0) 0) (by rw [wsetv_val_ne _ _ hne]; exact h1) hc
  exact WExec.seq e1 e2

/-- The fixed streams off the numerator and the scratch agree. -/
theorem fixed_agree {ω ω' : BS nw nn nsc nrs} (h : ∀ i, i ≠ tN → ¬ IsSc i → ω'.st i = ω.st i) (j : ℕ) (hj : j < 47)
    (h0 : j ≠ 0) (hs : j < 18 ∨ 25 ≤ j) : ω'.st (bst j hj) = ω.st (bst j hj) := by
  apply h
  · simp only [tN]; apply bst_ne; omega
  · simp only [IsSc, bst]; omega

theorem maskCom_of (cap : ℕ) (FP : GapParams) {n : ℕ} (c u v : BitInput n) {ω ω' : BS nw nn nsc nrs}
    (hc : MaskCom cap FP c u v ω) (h : ∀ i, i ≠ tN → ¬ IsSc i → ω'.st i = ω.st i) (hs : ω'.sh = ω.sh)
    (hv : ∀ (j : ℕ) (hj : j < 14), ω'.val (brg (122 + j) (by omega)) = 0) : MaskCom cap FP c u v ω' :=
  ⟨by rw [show tC = bst 1 _ from rfl, fixed_agree h 1 _ (by omega) (by omega)]; exact hc.C,
    by rw [show tU = bst 2 _ from rfl, fixed_agree h 2 _ (by omega) (by omega)]; exact hc.U,
    by rw [show tV = bst 3 _ from rfl, fixed_agree h 3 _ (by omega) (by omega)]; exact hc.V,
    by rw [show tSp = bst 4 _ from rfl, fixed_agree h 4 _ (by omega) (by omega)]; exact hc.Sp,
    by rw [show tThr = bst 36 _ from rfl, fixed_agree h 36 _ (by omega) (by omega)]; exact hc.Thr,
    fun i hi => by rw [hs]; exact hc.sh i hi, hv, hc.cap2⟩

theorem carOK_of (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n) (k : Fin 2)
    {ω ω' : BS nw nn nsc nrs} (hc : CarOK cap FP e X k ω) (h : ∀ i, i ≠ tN → ¬ IsSc i → ω'.st i = ω.st i) :
    CarOK cap FP e X k ω' := by
  have := k.isLt
  obtain ⟨A, B, ys, h1, h2, h3, h4⟩ := hc.acc
  exact ⟨by rw [show tG k = bst (32 + k.val) _ from rfl, fixed_agree h _ _ (by omega) (by omega)]; exact hc.G,
    ⟨A, B, ys, by rw [show tPos k = bst (10 + 4 * k.val) _ from rfl, fixed_agree h _ _ (by omega) (by omega)]; exact h1,
      by rw [show tNeg k = bst (11 + 4 * k.val) _ from rfl, fixed_agree h _ _ (by omega) (by omega)]; exact h2,
      by rw [show tX k = bst (12 + 4 * k.val) _ from rfl, fixed_agree h _ _ (by omega) (by omega)]; exact h3, h4⟩,
    by rw [show tZ k = bst (13 + 4 * k.val) _ from rfl, fixed_agree h _ _ (by omega) (by omega)]; exact hc.Z,
    by rw [show tT k = bst (8 + k.val) _ from rfl, fixed_agree h _ _ (by omega) (by omega)]; exact hc.T, hc.cap⟩

end Lay

/-! ## The step -/

variable (E : SymPtEval2)

/-- **The per-point step.** -/
noncomputable def ptStep : BP E.nw E.nn E.nsc E.nrs :=
  .seq maskAll (.seq (.ifr (rM 0) (.ifr (rM 1) (.seq (evalD E) addA) .skip) .skip) clearM)

/-- The step's cost: the mask, the evaluator's `nE`, the adder at `V` below `2^T`, the tests, the clearing. -/
def ptCost (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (nE V T : ℕ) : ℕ :=
  mkC FP e carriers 0 + 1 + 1 + (mkC FP e carriers 1 + 1) + 1 +
    (nE + 1 + (V * (incCost T + 4) + 1) + 2 + 1 + 5)

theorem ptStep_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (c u v : BitInput n) (W T x V nE : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs)
    (hcom : MaskCom cap FP c u v ω)
    (hcar : ∀ (k : Fin 2) (h : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, h⟩) k ω)
    (hM : ∀ k, ω.val (rM k) = 0) (hP : ∀ k : Fin 2, ω.val (rP k) = if k.val < carriers.length then 1 else 0)
    (hN : ω.st tN = frame (binary W x)) (hacc : ω.val rAcc = 0) (hac : ω.val rAc = 0)
    (hsc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false)
    (hev : ∀ ω₀ : BS E.nw E.nn E.nsc E.nrs, ω₀.sh = ω.sh → ω₀.cell = ω.cell →
      (∀ i, (∀ k : Fin 2, i ≠ tPos k ∧ i ≠ tNeg k ∧ i ≠ tX k) → ω₀.st i = ω.st i) →
      (∀ q, q ≠ rM 0 → q ≠ rM 1 → ω₀.val q = ω.val q) →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ nE ∧ EvOut V ω₀ ω₁)
    (hx : x + (carF FP e carriers c u v 0 && carF FP e carriers c u v 1).toNat * V < 2 ^ W)
    (hT : x + (carF FP e carriers c u v 0 && carF FP e carriers c u v 1).toNat * V < 2 ^ T)
    (hV : V ≤ cap) (hcap : 2 * T + 2 < cap) :
    ∃ ω', WExec cap (ptStep E) ω ω' (ptCost FP e carriers nE V T) ∧
      ω'.st tN = frame (binary W (x + (carF FP e carriers c u v 0 && carF FP e carriers c u v 1).toNat * V)) ∧
      MaskCom cap FP c u v ω' ∧
      (∀ (k : Fin 2) (h : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, h⟩) k ω') ∧
      ω'.val = ω.val ∧ ω'.sh = ω.sh ∧ ω'.cell = ω.cell ∧
      (∀ i, i ≠ tN → (∀ k : Fin 2, i ≠ tPos k ∧ i ≠ tNeg k ∧ i ≠ tX k) → ¬ IsSc i → ω'.st i = ω.st i) ∧
      (∀ i, IsSc i → ∀ b ∈ ω'.st i, b = false) := by
  obtain ⟨ω1, e1, c1, k1, o1, s1, v1, l1⟩ := maskAll_spec cap FP e carriers c u v ω hcom hcar hM hP
  have h01 : (rM 0 : Fin (bnr E.nn E.nrs)) ≠ rM 1 := fun h => by
    have := congrArg Fin.val h
    simp [rM, brg] at this
  have hA0 : (rAcc : Fin (bnr E.nn E.nrs)) ≠ rM 0 := by simp only [rAcc]; bne
  have hA1 : (rAcc : Fin (bnr E.nn E.nrs)) ≠ rM 1 := by simp only [rAcc]; bne
  have hC0 : (rAc : Fin (bnr E.nn E.nrs)) ≠ rM 0 := by simp only [rAc]; bne
  have hC1 : (rAc : Fin (bnr E.nn E.nrs)) ≠ rM 1 := by simp only [rAc]; bne
  have hCA : (rAc : Fin (bnr E.nn E.nrs)) ≠ rAcc := by simp only [rAc, rAcc]; apply brg_ne; omega
  have hNsc : ¬ IsSc (tN : Fin (bns E.nw E.nsc + 1)) := by simp only [IsSc, tN, bst]; omega
  have hNm : ∀ k : Fin 2, (tN : Fin (bns E.nw E.nsc + 1)) ≠ tPos k ∧ (tN : Fin (bns E.nw E.nsc + 1)) ≠ tNeg k ∧
      (tN : Fin (bns E.nw E.nsc + 1)) ≠ tX k := fun k => by
    have := k.isLt
    exact ⟨by bne, by bne, by bne⟩
  have hv1 : ∀ q, q ≠ rM 0 → q ≠ rM 1 → ω1.val q = ω.val q := fun q h0 h1 => by
    rw [v1, Function.update_of_ne h1, Function.update_of_ne h0]
  have hb0 : ω1.val (rM 0) = (carF FP e carriers c u v 0).toNat := by
    rw [v1, Function.update_of_ne h01, Function.update_self]
  have hb1 : ω1.val (rM 1) = (carF FP e carriers c u v 1).toNat := by rw [v1, Function.update_self]
  -- the middle: evaluate and add when both bits are `1`
  obtain ⟨ω3, e3, h3N, h3st, h3sc, h3v, h3s, h3c⟩ : ∃ ω3, WExec cap
      (.ifr (rM 0) (.ifr (rM 1) (.seq (evalD E) addA) .skip) .skip) ω1 ω3
      (nE + 1 + (V * (incCost T + 4) + 1) + 2) ∧
      ω3.st tN = frame (binary W (x + (carF FP e carriers c u v 0 && carF FP e carriers c u v 1).toNat * V)) ∧
      (∀ i, i ≠ tN → ¬ IsSc i → ω3.st i = ω1.st i) ∧ (∀ i, IsSc i → ∀ b ∈ ω3.st i, b = false) ∧
      ω3.val = ω1.val ∧ ω3.sh = ω1.sh ∧ ω3.cell = ω1.cell := by
    have hsc1 : ∀ i, IsSc i → ∀ b ∈ ω1.st i, b = false := fun i hi b hb => by
      have hi' : ∀ k : Fin 2, i ≠ tPos k ∧ i ≠ tNeg k ∧ i ≠ tX k := fun k => by
        have := k.isLt
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (subst h; simp only [IsSc, tPos, tNeg, tX, bst] at hi; omega)
      rw [o1 i hi'] at hb
      exact hsc i hi b hb
    have hN1 : ω1.st tN = frame (binary W x) := by rw [o1 tN hNm]; exact hN
    cases hf0 : carF FP e carriers c u v 0 <;> cases hf1 : carF FP e carriers c u v 1
    · refine ⟨ω1, WExec.mono (WExec.ifrF (by rw [hb0, hf0]; rfl) (WExec.skip ω1)) (by omega), ?_, fun i _ _ => rfl,
        hsc1, rfl, rfl, rfl⟩
      rw [hN1]; simp
    · refine ⟨ω1, WExec.mono (WExec.ifrF (by rw [hb0, hf0]; rfl) (WExec.skip ω1)) (by omega), ?_, fun i _ _ => rfl,
        hsc1, rfl, rfl, rfl⟩
      rw [hN1]; simp
    · refine ⟨ω1, WExec.mono (WExec.ifrT (by rw [hb0, hf0]; decide) (WExec.ifrF (by rw [hb1, hf1]; rfl)
        (WExec.skip ω1))) (by omega), ?_, fun i _ _ => rfl, hsc1, rfl, rfl, rfl⟩
      rw [hN1]; simp
    · obtain ⟨ω2, e2, ho⟩ := hev ω1 (by rw [s1]) l1 o1 hv1
      have hx' : x + V < 2 ^ W := by rw [hf0, hf1] at hx; simpa using hx
      have hT' : x + V < 2 ^ T := by rw [hf0, hf1] at hT; simpa using hT
      have e4 := addA_spec cap W T x V ω2 (by rw [ho.st tN hNsc]; exact hN1)
        (by rw [ho.sh, s1]; exact hcom.sh tN (by simp only [tN, tI]; apply bst_ne; omega))
        (by rw [ho.val, Function.update_of_ne hCA, hv1 rAc hC0 hC1]; exact hac)
        (by rw [ho.val, Function.update_self]) hx' hT' hV hcap
      refine ⟨_, WExec.ifrT (by rw [hb0, hf0]; decide) (WExec.ifrT (by rw [hb1, hf1]; decide)
        (WExec.seq e2 e4)), ?_, fun i hi hs => ?_, fun i hi b hb => ?_, ?_, ?_, ?_⟩
      · simp
      · simp only [WState.setv_st, WState.sets_st]
        rw [Function.update_of_ne hi]
        exact ho.st i hs
      · simp only [WState.setv_st, WState.sets_st] at hb
        have hi' : i ≠ tN := fun h => hNsc (h ▸ hi)
        rw [Function.update_of_ne hi'] at hb
        exact ho.sc i hi b hb
      · simp only [WState.setv_val, WState.sets_val]
        rw [ho.val, Function.update_idem]
        funext q
        by_cases hq : q = rAcc
        · subst hq
          rw [Function.update_self, hv1 rAcc hA0 hA1, hacc]
        · rw [Function.update_of_ne hq]
      · simp only [WState.setv_sh, WState.sets_sh]
        exact ho.sh
      · simp only [WState.setv_cell, WState.sets_cell]
        exact ho.cell
  -- clear the bits
  have e5 := clearM_spec cap ω3 (by rw [h3v, hb0]; cases carF FP e carriers c u v 0 <;> simp)
    (by rw [h3v, hb1]; cases carF FP e carriers c u v 1 <;> simp) (by have := hcom.cap2; omega)
  have hag : ∀ i, i ≠ tN → ¬ IsSc i → ((ω3.setv (rM 0) 0).setv (rM 1) 0).st i = ω1.st i := fun i hi hs => by
    simp only [WState.setv_st]
    exact h3st i hi hs
  have hfin : ((ω3.setv (rM 0) 0).setv (rM 1) 0).val = ω.val := by
    simp only [WState.setv_val]
    rw [h3v, v1]
    funext q
    by_cases hq1 : q = rM 1
    · subst hq1; rw [Function.update_self, hM 1]
    · rw [Function.update_of_ne hq1]
      by_cases hq0 : q = rM 0
      · subst hq0; rw [Function.update_self, hM 0]
      · rw [Function.update_of_ne hq0, Function.update_of_ne hq1, Function.update_of_ne hq0]
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e3 e5)) (by unfold ptCost; omega), ?_,
    maskCom_of cap FP c u v c1 hag ?_ (fun j hj => by rw [hfin]; exact hcom.ms j hj),
    fun k h => carOK_of cap FP e _ k (k1 k h) hag, hfin, ?_, ?_, fun i hi hm hs => ?_, fun i hi b hb => ?_⟩
  · simp only [WState.setv_st]
    exact h3N
  · simp only [WState.setv_sh]
    exact h3s
  · simp only [WState.setv_sh]
    rw [h3s, s1]
  · simp only [WState.setv_cell]
    rw [h3c, l1]
  · rw [hag i hi hs, o1 i hm]
  · simp only [WState.setv_st] at hb
    exact h3sc i hi b hb

end NearCubicWires.WireExponent3_5.FinalPass.Sd
