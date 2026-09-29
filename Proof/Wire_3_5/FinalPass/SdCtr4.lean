import Proof.Wire_3_5.FinalPass.SdCtr3

/-! # S4 (the seeds phase), part 13: one center (P3:1206-1216, 3046-3048)

**`cBody E`**: the center writer puts `c = centerAt P σ row col` on `tC`, the loop over the sampled pairs runs there,
and the pairs' word is rewound. **`cBody_spec`**: from the center loop's state `CInvB` at accumulator `a` (the row and
column words at `row`, `col`), the state `CInvB` at `a + sSum c` (the sampled pairs' terms at the center `c`), the row
and column words and the two flags unchanged. The evaluator is the center-level hypothesis `hevC` (from `PtEnvC`).

Paper quantity of the main type: `Σ_ℓ M(e, x_{c,ℓ})·Σ R̂(x_{c,ℓ})` at one center `c`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decCost decWord digitsOf)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)

variable (E : SymPtEval2)

/-- **One center**: the center written, the sampled pairs' loop, the pairs' word rewound. -/
noncomputable def cBody : BP E.nw E.nn E.nsc E.nrs := .seq ctrB (.seq (sLoop E) rewI)

/-- One center's cost. -/
def cbCost (FP : GapParams) (e : GapSeed FP) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (L s bb h tl nE Vm T : ℕ) :
    ℕ :=
  PrimT.Ctr.ctrCost P + 1 + ((L * (sCost FP e carriers s bb h tl nE Vm T + 2) + 1) + 1 +
    (5 * (0 + L * (2 * (2 * (s * h) + 1))) + 1))

theorem cBody_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm : ℕ) (ωR0 : BS E.nw E.nn E.nsc E.nrs)
    (hR : CStat cap FP carriers P σT ps s bb h tl ωR0)
    (hbs : bb + 1 = 2 ^ s) (hn : h * bb + h * bb + tl = P.n) (hkh : 1 ≤ s * h)
    (hdl : ∀ a : Fin N, decWord bb h tl false (digitsOf s h (binary (s * h) a)) = List.ofFn (eu a))
    (hdr : ∀ b : Fin N, decWord bb h tl true (digitsOf s h (binary (s * h) b)) = List.ofFn (ev b))
    (hevC : ∀ (c : BitInput P.n) (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs), PtEnvC c (eu a) (ev b) ωR0 ω₀ →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ nE ∧ EvOut (Vf c a b) ω₀ ω₁)
    (hVm : ∀ c a b, Vf c a b ≤ Vm) (hVc : Vm ≤ cap) (hcapT : 2 * T + 2 < cap)
    (hcs : 2 * 2 ^ s ≤ cap ∧ s ≤ cap ∧ 2 * P.n ≤ cap ∧ bb ≤ cap ∧ h ≤ cap ∧ tl ≤ cap)
    (hp : ps.length * (2 * (2 * (s * h) + 1)) ≤ cap) (h8 : 8 * (P.n + 2) ≤ cap)
    (row col a : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs) (hJ : CInvB cap FP e carriers W a ωR0 ω)
    (hrow : ω.st tRow = frame (binary (dRow P) row)) (hcol : ω.st tCol = frame (binary (dR P) col))
    (hx : a + sSum FP e carriers (centerAt P σT row col) eu ev (Vf (centerAt P σT row col)) ps < 2 ^ W)
    (hT : a + sSum FP e carriers (centerAt P σT row col) eu ev (Vf (centerAt P σT row col)) ps < 2 ^ T) :
    ∃ ω', WExec cap (cBody E) ω ω' (cbCost FP e P carriers ps.length s bb h tl nE Vm T) ∧
      CInvB cap FP e carriers W (a + sSum FP e carriers (centerAt P σT row col) eu ev (Vf (centerAt P σT row col)) ps)
        ωR0 ω' ∧
      ω'.st tRow = ω.st tRow ∧ ω'.st tCol = ω.st tCol ∧ (∀ b : Bool, ω'.val (cF b) = ω.val (cF b)) := by
  -- facts about the fixed streams and registers
  have kC : ∀ (j : ℕ) (hj : j < 47), j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 25 → j ≠ 26 → (j < 10 ∨ 18 ≤ j) →
      (j < 18 ∨ 25 ≤ j) → KeptC (bst j hj : Fin (bns E.nw E.nsc + 1)) := fun j hj h0 h1 h2 h3 h25 h26 hm hs =>
    ⟨kept_bst j hj h0 h2 h3 hm hs, by simp only [tC]; apply bst_ne; omega, by simp only [tRow]; apply bst_ne; omega,
      by simp only [tCol]; apply bst_ne; omega⟩
  have fl : ∀ (j : ℕ) (hj : j < 220), j ≠ 195 → j ≠ 198 →
      ((brg j hj : Fin (bnr E.nn E.nrs)) ≠ cF false ∧ (brg j hj : Fin (bnr E.nn E.nrs)) ≠ cF true) :=
    fun j hj h1 h2 => ⟨by simp only [cF]; apply brg_ne; simp; omega, by simp only [cF]; apply brg_ne; simp; omega⟩
  have hRv : ∀ (j : ℕ) (hj : j < 220), j ≠ 195 → j ≠ 198 → ω.val (brg j hj) = ωR0.val (brg j hj) :=
    fun j hj h1 h2 => hJ.val _ (fl j hj h1 h2).1 (fl j hj h1 h2).2
  have hsh0 : ∀ i, ω.sh i = 0 := fun i => by rw [hJ.sh]; exact hR.sh i
  have hCk : ∀ i, KeptC i → i ≠ (tC : Fin (bns E.nw E.nsc + 1)) := fun i hi => hi.2.1
  -- the center
  obtain ⟨YC, hYC, hlC⟩ := hJ.C
  obtain ⟨ωc, ec, hc, hco, hcs', hcv, hcc⟩ := ctrB_spec cap P σT row col ω
    (by
      rw [hJ.st (ctrS 0) (kC 30 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega))]
      exact hR.off)
    hrow hcol (by rw [hYC]; simp [hlC]) (fun i => hsh0 _)
    (by
      rw [show (ctrR 0 : Fin (bnr E.nn E.nrs)) = brg 168 (by omega) from rfl, hRv 168 _ (by omega) (by omega)]
      exact hR.cB)
    (by
      rw [show (ctrR 1 : Fin (bnr E.nn E.nrs)) = brg 169 (by omega) from rfl, hRv 169 _ (by omega) (by omega)]
      exact hR.cS)
    (by
      rw [show (ctrR 2 : Fin (bnr E.nn E.nrs)) = brg 170 (by omega) from rfl, hRv 170 _ (by omega) (by omega)]
      exact hR.cH)
    (by
      rw [show (ctrR 3 : Fin (bnr E.nn E.nrs)) = brg 171 (by omega) from rfl, hRv 171 _ (by omega) (by omega)]
      exact hR.cL)
    (by
      rw [show (ctrR 4 : Fin (bnr E.nn E.nrs)) = brg 172 (by omega) from rfl, hRv 172 _ (by omega) (by omega)]
      exact hR.cR)
    (fun i hi => by
      have := i.isLt
      rw [show (ctrR i : Fin (bnr E.nn E.nrs)) = brg (168 + i.val) (by omega) from rfl,
        hRv _ _ (by omega) (by omega)]
      exact hR.cZ i hi)
    h8
  have hωc_st : ∀ i, i ≠ tC → ωc.st i = ω.st i := hco
  -- the sample loop's static facts at ωc
  have hS : SStat cap FP carriers (centerAt P σT row col) s bb h tl ωc :=
    ⟨by rw [hc, frame_eq_frameP],
      by
        rw [hωc_st _ (by simp only [tSp, tC]; apply bst_ne; omega),
          hJ.st tSp (kC 4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
        exact hR.Sp,
      by
        rw [hωc_st _ (by simp only [tThr, tC]; apply bst_ne; omega),
          hJ.st tThr (kC 36 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega))]
        exact hR.Thr,
      fun i _ => by rw [hcs']; exact hsh0 i,
      fun j hj => by rw [hcv, hRv _ _ (by omega) (by omega)]; exact hR.ms j hj,
      hR.cap2,
      fun k => by
        have := k.isLt
        rw [hcv, show (rM k : Fin (bnr E.nn E.nrs)) = brg (118 + k.val) (by omega) from rfl,
          hRv _ _ (by omega) (by omega)]
        exact hR.M k,
      fun k => by
        have := k.isLt
        rw [hcv, show (rP k : Fin (bnr E.nn E.nrs)) = brg (120 + k.val) (by omega) from rfl,
          hRv _ _ (by omega) (by omega)]
        exact hR.Pf k,
      by
        rw [hcv, show (rAcc : Fin (bnr E.nn E.nrs)) = brg 0 (by omega) from rfl, hRv _ _ (by omega) (by omega)]
        exact hR.acc,
      by
        rw [hcv, show (rAc : Fin (bnr E.nn E.nrs)) = brg 154 (by omega) from rfl, hRv _ _ (by omega) (by omega)]
        exact hR.ac,
      fun q hq => by
        have := q.isLt
        rw [hcv, show (frD q : Fin (bnr E.nn E.nrs)) = brg (156 + q.val) (by omega) from rfl,
          hRv _ _ (by omega) (by omega), show (brg (156 + q.val) _ : Fin (bnr E.nn E.nrs)) = frD q from rfl,
          hR.dec q]⟩
  have hX0 : ωc.val rgX = 0 := by
    rw [hcv, show (rgX : Fin (bnr E.nn E.nrs)) = brg 165 (by omega) from rfl, hRv _ _ (by omega) (by omega),
      show (brg 165 _ : Fin (bnr E.nn E.nrs)) = frD 9 from rfl, hR.dec 9]
    rfl
  have hNC : (tN : Fin (bns E.nw E.nsc + 1)) ≠ tC := by simp only [tN, tC]; apply bst_ne; omega
  have hUC : (tU : Fin (bns E.nw E.nsc + 1)) ≠ tC := by simp only [tU, tC]; apply bst_ne; omega
  have hVC : (tV : Fin (bns E.nw E.nsc + 1)) ≠ tC := by simp only [tV, tC]; apply bst_ne; omega
  have hIC : (tI : Fin (bns E.nw E.nsc + 1)) ≠ tC := by simp only [tI, tC]; apply bst_ne; omega
  have hIk : KeptC (tI : Fin (bns E.nw E.nsc + 1)) :=
    kC 31 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨YU, hYU, hlU⟩ := hJ.U
  obtain ⟨YV, hYV, hlV⟩ := hJ.V
  have hI0 : SInv cap FP e carriers (s * h) W a 0 ps ωc ωc :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, by rw [hcs']; exact hsh0 _, fun _ _ => rfl, hX0, rfl,
      by rw [hωc_st _ hNC]; exact hJ.Nw, ⟨YU, by rw [hωc_st _ hUC]; exact hYU, hlU⟩,
      ⟨YV, by rw [hωc_st _ hVC]; exact hYV, hlV⟩,
      fun k hk => carOK_tr cap FP e _ k (hJ.car k hk) (fun j hj hj' => hωc_st _
        (by simp only [tC]; apply bst_ne; omega)),
      fun i hi b hb => by
        rw [hωc_st i (fun h => by subst h; simp only [IsSc, tC, bst] at hi; omega)] at hb
        exact hJ.sc i hi b hb,
      by rw [List.drop_zero, hωc_st _ hIC, hJ.st _ hIk]; exact hR.I⟩
  -- the pairs
  obtain ⟨ω2, e2, hI2⟩ := sLoop_spec E cap FP e carriers (centerAt P σT row col) eu ev (Vf (centerAt P σT row col))
    s bb h tl W T nE Vm ωc hS hbs hn hkh hdl hdr
    (fun a' b' ω₀ hP => hevC (centerAt P σT row col) a' b' ω₀
      ⟨fun i hi => by rw [hP.st i hi.1, hωc_st i hi.2.1]; exact hJ.st i hi,
        by rw [hP.st tC kept_C, hc, frame_eq_frameP], hP.U, hP.V,
        fun i hi => by rw [hP.sh i hi, hcs', hJ.sh],
        fun q hq h0 h1 hf0 hf1 => by rw [hP.val q hq h0 h1, hcv]; exact hJ.val q hf0 hf1,
        by rw [hP.cell, hcc]; exact hJ.cell, hP.sc⟩)
    (fun a' b' => hVm _ a' b') hVc hcapT hcs ps a 0 ωc hI0 (by omega) hx hT
  -- the pairs' word rewound
  have e3 := rewI_spec cap (0 + ps.length * (2 * (2 * (s * h) + 1))) ω2 hI2.X hI2.shI (by omega)
  refine ⟨_, WExec.seq ec (WExec.seq e2 e3), ⟨fun i hi => ?_, ?_, fun q hq1 hq2 => ?_, ?_, ?_, ?_, ?_, ?_,
    fun k hk => carOK_tr cap FP e _ k (hI2.car k hk) (fun _ _ _ => rfl), fun i hi b hb => ?_⟩, ?_, ?_, fun b => ?_⟩
  · simp only [WState.seth_st, WState.setv_st]
    rw [hI2.st i hi.1, hωc_st i hi.2.1]
    exact hJ.st i hi
  · funext i
    simp only [WState.seth_sh, WState.setv_sh]
    by_cases hi : i = tI
    · subst hi
      rw [Function.update_self, hR.sh]
    · rw [Function.update_of_ne hi, hI2.sh i hi, hcs', hJ.sh]
  · simp only [WState.seth_val, WState.setv_val]
    by_cases hx9 : q = rgX
    · subst hx9
      rw [Function.update_self, show (rgX : Fin (bnr E.nn E.nrs)) = frD 9 from rfl, hR.dec 9]
      rfl
    · rw [Function.update_of_ne hx9, hI2.val q hx9, hcv]
      exact hJ.val q hq1 hq2
  · simp only [WState.seth_cell, WState.setv_cell]
    rw [hI2.cell, hcc]
    exact hJ.cell
  · simp only [WState.seth_st, WState.setv_st]
    exact hI2.Nw
  · simp only [WState.seth_st, WState.setv_st]
    exact hI2.U
  · simp only [WState.seth_st, WState.setv_st]
    exact hI2.V
  · simp only [WState.seth_st, WState.setv_st]
    refine ⟨List.ofFn (centerAt P σT row col), ?_, by simp⟩
    rw [hI2.st tC kept_C, hc]
  · simp only [WState.seth_st, WState.setv_st] at hb
    exact hI2.sc i hi b hb
  · simp only [WState.seth_st, WState.setv_st]
    rw [hI2.st tRow kept_Row, hωc_st _ (by simp only [tRow, tC]; apply bst_ne; omega)]
  · simp only [WState.seth_st, WState.setv_st]
    rw [hI2.st tCol kept_Col, hωc_st _ (by simp only [tCol, tC]; apply bst_ne; omega)]
  · have hne : (cF b : Fin (bnr E.nn E.nrs)) ≠ rgX := by
      simp only [cF, rgX]; apply brg_ne; split <;> omega
    simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne hne, hI2.val _ hne, hcv]

end NearCubicWires.WireExponent3_5.FinalPass.Sd
