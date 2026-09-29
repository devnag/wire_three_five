import Proof.Wire_3_5.FinalPass.SdSeedQ

/-! # S4 (the seeds phase), part 20: one filter seed's run (P3:2036-2101, 3044-3048)

**`seedIter_spec`**: from the seed loop's state `SdInv` at accumulator `x` (the tables word `twW (e :: rest)` at the
saved position `p`, the seed flag set), `seedBody E` reaches `SdInv` at `x + Gs e` (`ctrLoop_spec` at the state
after the seed's tables are in place, `ctrLoop_sum`), the saved position past the seed and the flag `[rest ≠ []]`
(`twW_head`).

Paper quantity of the main type: one filter seed's term `Σ_c Σ_ℓ M(e, x_{c,ℓ})·Σ R̂(x_{c,ℓ})`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)
open NearCubicWires.SupplierWalk (majorityThreshold)

section Lay
variable {nw nn nsc nrs : ℕ}

theorem tT_ne_tTW (k : Fin 2) : (tT k : Fin (bns nw nsc + 1)) ≠ tTW := by
  have := k.isLt; simp only [tT, tTW]; apply bst_ne; omega

theorem tT01 : (tT 0 : Fin (bns nw nsc + 1)) ≠ tT 1 := by simp only [tT]; apply bst_ne; simp

theorem cpOut_st (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) (i : Fin (bns nw nsc + 1))
    (hi : i ≠ tT k) : (cpOut k w p ω).st i = ω.st i := by
  simp only [cpOut, WState.setv_st, WState.seth_st, WState.sets_st]
  rw [Function.update_of_ne hi]

theorem cpOut_st_T (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) : (cpOut k w p ω).st (tT k) = w := by
  simp [cpOut]

theorem cpOut_sh (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) (i : Fin (bns nw nsc + 1))
    (hi : i ≠ tTW) : (cpOut k w p ω).sh i = ω.sh i := by
  simp only [cpOut, WState.setv_sh, WState.seth_sh, WState.sets_sh]
  rw [Function.update_of_ne hi]

theorem cpOut_sh_W (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) : (cpOut k w p ω).sh tTW = p := by
  simp [cpOut]

theorem cpOut_val (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) (q : Fin (bnr nn nrs)) (hq : q ≠ rgT) :
    (cpOut k w p ω).val q = ω.val q := by
  simp only [cpOut, WState.setv_val, WState.seth_val, WState.sets_val]
  rw [Function.update_of_ne hq]

theorem cpOut_val_T (k : Fin 2) (w : List Bool) (p : ℕ) (ω : BS nw nn nsc nrs) : (cpOut k w p ω).val rgT = p := by
  simp [cpOut]

theorem kept_tTW : KeptC (tTW : Fin (bns nw nsc + 1)) :=
  ⟨kept_bst 27 _ (by omega) (by omega) (by omega) (by omega) (by omega),
    by simp only [tTW, tC]; apply bst_ne; omega, by simp only [tTW, tRow]; apply bst_ne; omega,
    by simp only [tTW, tCol]; apply bst_ne; omega⟩

theorem keptC_T (k : Fin 2) : KeptC (tT k : Fin (bns nw nsc + 1)) := by
  have := k.isLt
  exact ⟨kept_bst (8 + k.val) _ (by omega) (by omega) (by omega) (by omega) (by omega),
    by simp only [tT, tC]; apply bst_ne; omega, by simp only [tT, tRow]; apply bst_ne; omega,
    by simp only [tT, tCol]; apply bst_ne; omega⟩

theorem bst_ne_T (j : ℕ) (hj : j < 47) (k : Fin 2) (h8 : j ≠ 8) (h9 : j ≠ 9) :
    (bst j hj : Fin (bns nw nsc + 1)) ≠ tT k := by
  have := k.isLt
  simp only [tT]; apply bst_ne; omega

theorem isSc_T (i : Fin (bns nw nsc + 1)) (hi : IsSc i) (k : Fin 2) : i ≠ tT k := by
  have := k.isLt
  rintro rfl
  simp only [IsSc, tT, bst] at hi
  omega

theorem cT_ne_T (row : Bool) (k : Fin 2) : (cT row : Fin (bns nw nsc + 1)) ≠ tT k := by
  have := k.isLt
  simp only [cT, tT]; apply bst_ne; split <;> omega

theorem cReg_ne (row : Bool) :
    (cC row : Fin (bnr nn nrs)) ≠ rgP ∧ (cC row : Fin (bnr nn nrs)) ≠ fS ∧ (cF row : Fin (bnr nn nrs)) ≠ rgP ∧
      (cF row : Fin (bnr nn nrs)) ≠ fS ∧ (cK row : Fin (bnr nn nrs)) ≠ rgP ∧ (cK row : Fin (bnr nn nrs)) ≠ fS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cC, cF, cK, rgP, fS] <;> apply brg_ne <;> split <;> omega

theorem rgT_ne_cF (row : Bool) : (rgT : Fin (bnr nn nrs)) ≠ cF row := by
  simp only [rgT, cF]; apply brg_ne; split <;> omega

end Lay

variable (E : SymPtEval2)

/-- **One filter seed's run.** -/
theorem seedIter_spec (cap : ℕ) (FP : GapParams) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm Bd : ℕ) (ωQ : BS E.nw E.nn E.nsc E.nrs)
    (H : QHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ωQ) (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T)
    (e : GapSeed FP) (rest : List (GapSeed FP)) (x p : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs)
    (hI : SdInv FP P carriers W x ωQ ω) (hP : ω.val rgP = p) (hF : ω.val fS = 1)
    (hTW : (ω.st tTW).drop p = twW FP (e :: rest) (Seams.carLen carriers 0) (Seams.carLen carriers 1))
    (hb : x + Gs FP e P σT carriers ps eu ev Vf ≤ Bd) :
    ∃ ω', WExec cap (seedBody E) ω ω' (sbCost FP e P carriers ps.length s bb h tl nE Vm T (ωQ.st tTW).length) ∧
      SdInv FP P carriers W (x + Gs FP e P σT carriers ps eu ev Vf) ωQ ω' ∧
      ω'.val rgP = p + (2 * (tb FP e (Seams.carLen carriers 0)).length + 1) +
        (2 * (tb FP e (Seams.carLen carriers 1)).length + 1) ∧
      ω'.val fS = (decide (rest ≠ [])).toNat ∧
      (ω'.st tTW).drop (p + (2 * (tb FP e (Seams.carLen carriers 0)).length + 1) +
        (2 * (tb FP e (Seams.carLen carriers 1)).length + 1)) =
        twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1) := by
  obtain ⟨t0, ht0⟩ : ∃ t, t = tb FP e (Seams.carLen carriers 0) := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ : ∃ t, t = tb FP e (Seams.carLen carriers 1) := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ q, q = p + (2 * t0.length + 1) + (2 * t1.length + 1) := ⟨_, rfl⟩
  rw [← ht0, ← ht1, ← hp2]
  -- the facts at entry
  have hsh0 : ∀ i, ω.sh i = 0 := fun i => by rw [hI.sh]; exact H.R.sh i
  have hTWQ : ω.st tTW = ωQ.st tTW := hI.st tTW kept_tTW (tT_ne_tTW 0).symm (tT_ne_tTW 1).symm
  have hLwc : (ω.st tTW).length + 1 < cap := by rw [hTWQ]; exact H.twc
  have hdrop : (ω.st tTW).drop p = frameP t0 ++ false :: (frameP t1 ++ false ::
      twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1)) := by
    rw [hTW, twW_cons, ← ht0, ← ht1]
  have hl : p2 + 1 ≤ (ω.st tTW).length := by
    have el := congrArg List.length hdrop
    have htw : 1 ≤ (twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length := by simp [twW]
    simp only [List.length_drop, List.length_append, frameP_length, List.length_cons] at el
    omega
  have hLw : p2 + 1 ≤ (ωQ.st tTW).length := by rw [← hTWQ]; exact hl
  have hd1 : (ω.st tTW).drop (p + 2 * t0.length + 1) = frameP t1 ++ false ::
      twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1) := by
    rw [show p + 2 * t0.length + 1 = p + (2 * t0.length + 1) by omega, ← List.drop_drop, hdrop, drop_frame]
  have hd2 : (ω.st tTW).drop p2 = twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1) := by
    rw [show p2 = (p + 2 * t0.length + 1) + (2 * t1.length + 1) by omega, ← List.drop_drop, hd1, drop_frame]
  have hTv : ω.val rgT = 0 := by rw [hI.val _ rgP_ne_T.symm fS_ne_T.symm]; exact H.regT
  have nBT : (rgB : Fin (bnr E.nn E.nrs)) ≠ rgT := by simp only [rgB, rgT]; apply brg_ne; omega
  have nBP : (rgB : Fin (bnr E.nn E.nrs)) ≠ rgP := by simp only [rgB, rgP]; apply brg_ne; omega
  have nBF : (rgB : Fin (bnr E.nn E.nrs)) ≠ fS := by simp only [rgB, fS]; apply brg_ne; omega
  have hBv : ω.val rgB = 0 := by rw [hI.val _ nBP nBF]; exact H.regB
  have hT0 : (ω.st (tT 0)).length = t0.length := by rw [ht0, tb, tab_len]; exact hI.T 0
  have hT1 : (ω.st (tT 1)).length = t1.length := by rw [ht1, tb, tab_len]; exact hI.T 1
  -- 1: the flag down
  have e1 := WExec.dec (cap := cap) fS ω (by rw [hF]; have := H.R.cap2; omega)
  rw [hF, Nat.sub_self] at e1
  -- 2: `tTW` to the saved position
  have e2 := fwdP_spec cap p (ω.setv fS 0) (by rw [WState.setv_sh]; exact hsh0 _)
    (by rw [wsetv_val_ne _ _ fS_ne_T.symm]; exact hTv) (by rw [wsetv_val_ne _ _ fS_ne_P.symm]; exact hP) (by omega)
  obtain ⟨ω2, h2⟩ : ∃ y, y = (((ω.setv fS 0).setv rgP 0).setv rgT p).seth tTW p := ⟨_, rfl⟩
  rw [← h2] at e2
  have st2 : ω2.st = ω.st := by rw [h2]; simp
  have sh2 : ω2.sh = Function.update ω.sh tTW p := by rw [h2]; simp
  have v2T : ω2.val rgT = p := by rw [h2]; simp
  have v2P : ω2.val rgP = 0 := by rw [h2, WState.seth_val, wsetv_val_ne _ _ rgP_ne_T]; simp
  have v2F : ω2.val fS = 0 := by rw [h2, WState.seth_val, wsetv_val_ne _ _ fS_ne_T, wsetv_val_ne _ _ fS_ne_P]; simp
  have v2B : ω2.val rgB = 0 := by
    rw [h2, WState.seth_val, wsetv_val_ne _ _ nBT, wsetv_val_ne _ _ nBP, wsetv_val_ne _ _ nBF]; exact hBv
  -- 3: carrier 0's table
  have e3 := cpTB_spec cap 0 t0 (ω2.st (tT 0)) (frameP t1 ++ false ::
      twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1)) p ω2 (by rw [st2]; exact hT0) (by omega)
    (by rw [st2]; exact hdrop) (by rw [sh2, Function.update_self]) v2T rfl
    (by rw [sh2, Function.update_of_ne (tT_ne_tTW 0)]; exact hsh0 _) v2B
  obtain ⟨ω3, h3⟩ : ∃ y, y = cpOut 0 t0 (p + 2 * t0.length + 1) ω2 := ⟨_, rfl⟩
  rw [← h3] at e3
  -- 4: carrier 1's table
  have e4 := cpTB_spec cap 1 t1 (ω3.st (tT 1)) (twW FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1))
    (p + 2 * t0.length + 1) ω3 (by rw [h3, cpOut_st _ _ _ _ _ tT01.symm, st2]; exact hT1) (by omega)
    (by rw [h3, cpOut_st _ _ _ _ _ (tT_ne_tTW 0).symm, st2]; exact hd1) (by rw [h3, cpOut_sh_W])
    (by rw [h3, cpOut_val_T]) rfl
    (by rw [h3, cpOut_sh _ _ _ _ _ (tT_ne_tTW 1), sh2, Function.update_of_ne (tT_ne_tTW 1)]; exact hsh0 _)
    (by rw [h3, cpOut_val _ _ _ _ _ nBT]; exact v2B)
  rw [show p + 2 * t0.length + 1 + 2 * t1.length + 1 = p2 by omega] at e4
  obtain ⟨ω4, h4⟩ : ∃ y, y = cpOut 1 t1 p2 ω3 := ⟨_, rfl⟩
  rw [← h4] at e4
  -- 5: `tTW` back, its position saved
  have e5 := rewP_spec cap p2 ω4 (by rw [h4, cpOut_sh_W]) (by rw [h4, cpOut_val_T])
    (by rw [h4, cpOut_val _ _ _ _ _ rgP_ne_T, h3, cpOut_val _ _ _ _ _ rgP_ne_T]; exact v2P) (by omega)
  obtain ⟨ω5, h5⟩ : ∃ y, y = ((ω4.setv rgT 0).setv rgP p2).seth tTW 0 := ⟨_, rfl⟩
  rw [← h5] at e5
  -- the center loop's entry state
  have st5 : ∀ i, i ≠ tT 0 → i ≠ tT 1 → ω5.st i = ω.st i := fun i hi0 hi1 => by
    rw [h5, WState.seth_st, WState.setv_st, WState.setv_st, h4, cpOut_st _ _ _ _ _ hi1, h3, cpOut_st _ _ _ _ _ hi0,
      st2]
  have stT0 : ω5.st (tT 0) = t0 := by
    rw [h5, WState.seth_st, WState.setv_st, WState.setv_st, h4, cpOut_st _ _ _ _ _ tT01, h3, cpOut_st_T]
  have stT1 : ω5.st (tT 1) = t1 := by
    rw [h5, WState.seth_st, WState.setv_st, WState.setv_st, h4, cpOut_st_T]
  have hTg : ∀ k : Fin 2, ω5.st (tT k) = tb FP e (Seams.carLen carriers k.val) := by
    intro k
    fin_cases k
    · exact stT0.trans ht0
    · exact stT1.trans ht1
  have sh5 : ω5.sh = ω.sh := by
    funext i
    rw [h5]
    simp only [WState.seth_sh, WState.setv_sh]
    by_cases hi : i = tTW
    · subst hi
      rw [Function.update_self]
      exact (hsh0 _).symm
    · rw [Function.update_of_ne hi, h4, cpOut_sh _ _ _ _ _ hi, h3, cpOut_sh _ _ _ _ _ hi, sh2,
        Function.update_of_ne hi]
  have val5 : ∀ q, q ≠ rgP → q ≠ fS → ω5.val q = ω.val q := by
    intro q hqP hqF
    rw [h5, WState.seth_val, wsetv_val_ne _ _ hqP]
    by_cases hqT : q = rgT
    · rw [hqT, wsetv_val_self, hTv]
    · rw [wsetv_val_ne _ _ hqT, h4, cpOut_val _ _ _ _ _ hqT, h3, cpOut_val _ _ _ _ _ hqT, h2, WState.seth_val,
        wsetv_val_ne _ _ hqT, wsetv_val_ne _ _ hqP, wsetv_val_ne _ _ hqF]
  have v5P : ω5.val rgP = p2 := by rw [h5]; simp
  have v5F : ω5.val fS = 0 := by
    rw [h5, WState.seth_val, wsetv_val_ne _ _ fS_ne_P, wsetv_val_ne _ _ fS_ne_T, h4, cpOut_val _ _ _ _ _ fS_ne_T, h3,
      cpOut_val _ _ _ _ _ fS_ne_T]
    exact v2F
  have cell5 : ω5.cell = ω.cell := by rw [h5, h4, h3, h2]; simp [cpOut]
  have hne : ∀ (j : ℕ) (hj : j < 47), j ≠ 8 → j ≠ 9 → ω5.st (bst j hj) = ω.st (bst j hj) := fun j hj h8 h9 =>
    st5 _ (bst_ne_T j hj 0 h8 h9) (bst_ne_T j hj 1 h8 h9)
  have hst5Q : ∀ i, KeptC i → i ≠ tT 0 → i ≠ tT 1 → ω5.st i = ωQ.st i := fun i hk hi0 hi1 => by
    rw [st5 i hi0 hi1]; exact hI.st i hk hi0 hi1
  have hsh5Q : ω5.sh = ωQ.sh := by rw [sh5]; exact hI.sh
  have hval5Q : ∀ q, q ≠ rgP → q ≠ fS → ω5.val q = ωQ.val q := fun q hqP hqF => by
    rw [val5 q hqP hqF]; exact hI.val q hqP hqF
  have hcell5Q : ω5.cell = ωQ.cell := by rw [cell5]; exact hI.cell
  have HC : CHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ω5 :=
    ⟨cStat_tr cap FP carriers P σT ps s bb h tl ωQ ω5 H.R hst5Q hsh5Q
        (fun j hj hj2 => hval5Q _ (by simp only [rgP]; apply brg_ne; omega) (by simp only [fS]; apply brg_ne; omega)),
      H.bs, H.n, H.kh, H.dl, H.dr, H.evq ω5 hst5Q hsh5Q hval5Q hcell5Q, H.Vle, H.Vc, H.capT, H.cs, H.p, H.c8, H.dT,
      H.c2⟩
  have hInv : CInvB cap FP e carriers W x ω5 ω5 := by
    obtain ⟨YU, hYU, hlU⟩ := hI.U
    obtain ⟨YV, hYV, hlV⟩ := hI.V
    obtain ⟨YC, hYC, hlC⟩ := hI.C
    refine ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, ?_, ⟨YU, ?_, hlU⟩, ⟨YV, ?_, hlV⟩, ⟨YC, ?_, hlC⟩, ?_, ?_⟩
    · rw [show (tN : Fin (bns E.nw E.nsc + 1)) = bst 0 (by omega) from rfl, hne 0 _ (by omega) (by omega)]
      exact hI.Nw
    · rw [show (tU : Fin (bns E.nw E.nsc + 1)) = bst 2 (by omega) from rfl, hne 2 _ (by omega) (by omega)]
      exact hYU
    · rw [show (tV : Fin (bns E.nw E.nsc + 1)) = bst 3 (by omega) from rfl, hne 3 _ (by omega) (by omega)]
      exact hYV
    · rw [show (tC : Fin (bns E.nw E.nsc + 1)) = bst 1 (by omega) from rfl, hne 1 _ (by omega) (by omega)]
      exact hYC
    · intro k hk
      have hc := hI.car k hk
      have := k.isLt
      obtain ⟨A, B, ys, a1, a2, a3, a4⟩ := hc.acc
      refine ⟨?_, ⟨A, B, ys, ?_, ?_, ?_, a4⟩, ?_, ?_, H.mkc e k hk⟩
      · rw [show (tG k : Fin (bns E.nw E.nsc + 1)) = bst (32 + k.val) (by omega) from rfl,
          hne _ _ (by omega) (by omega)]
        exact hc.G
      · rw [show (tPos k : Fin (bns E.nw E.nsc + 1)) = bst (10 + 4 * k.val) (by omega) from rfl,
          hne _ _ (by omega) (by omega)]
        exact a1
      · rw [show (tNeg k : Fin (bns E.nw E.nsc + 1)) = bst (11 + 4 * k.val) (by omega) from rfl,
          hne _ _ (by omega) (by omega)]
        exact a2
      · rw [show (tX k : Fin (bns E.nw E.nsc + 1)) = bst (12 + 4 * k.val) (by omega) from rfl,
          hne _ _ (by omega) (by omega)]
        exact a3
      · rw [show (tZ k : Fin (bns E.nw E.nsc + 1)) = bst (13 + 4 * k.val) (by omega) from rfl,
          hne _ _ (by omega) (by omega)]
        exact hc.Z
      · rw [hTg k, tb, Seams.carLen, dif_pos hk]
    · intro i hi b hb
      rw [st5 i (isSc_T i hi 0) (isSc_T i hi 1)] at hb
      exact hI.sc i hi b hb
  have hCnt : ∀ (row : Bool) (d : ℕ), CntAt row d 0 0 ω → CntAt row d 0 0 ω5 := fun row d hc =>
    ⟨by rw [st5 _ (cT_ne_T row 0) (cT_ne_T row 1)]; exact hc.st, by rw [sh5]; exact hc.sh,
      by rw [val5 _ (cReg_ne row).1 (cReg_ne row).2.1]; exact hc.c,
      by rw [val5 _ (cReg_ne row).2.2.1 (cReg_ne row).2.2.2.1]; exact hc.f,
      by rw [val5 _ (cReg_ne row).2.2.2.2.1 (cReg_ne row).2.2.2.2.2]; exact hc.k⟩
  -- 6: the center loop
  have hsum : ∑ y ∈ Finset.Ico 0 (2 ^ dRow P), Sd.rG FP e P σT carriers ps eu ev Vf y =
      Gs FP e P σT carriers ps eu ev Vf := ctrLoop_sum FP e P σT carriers ps eu ev Vf
  obtain ⟨ω6, e6, hI6, hCc6, hCr6⟩ := ctrLoop_spec E cap FP e P σT carriers ps eu ev Vf s bb h tl W T nE Vm Bd ω5
    HC hBW hBT x ω5 hInv (hCnt false _ hI.cc) (hCnt true _ hI.cr) (by rw [hsum]; exact hb)
  have hsh6 : ω6.sh = ω.sh := by rw [hI6.sh, sh5]
  have st6W : ω6.st tTW = ω.st tTW := by
    rw [hI6.st tTW kept_tTW, st5 _ (tT_ne_tTW 0).symm (tT_ne_tTW 1).symm]
  -- 7: the next seed's test
  have e7 := peek_spec cap p2 ω6 (by rw [hsh6]; exact hsh0 _)
    (by rw [hI6.val _ (rgT_ne_cF false) (rgT_ne_cF true), val5 _ rgP_ne_T.symm fS_ne_T.symm]; exact hTv)
    (by rw [hI6.val _ (cReg_ne false).2.2.1.symm (cReg_ne true).2.2.1.symm]; exact v5P)
    (by rw [hI6.val _ (cReg_ne false).2.2.2.1.symm (cReg_ne true).2.2.2.1.symm]; exact v5F) (by omega)
  obtain ⟨ω7, h7⟩ : ∃ y, y = ω6.setv fS (readTapeBit (ω6.st tTW) p2).toNat := ⟨_, rfl⟩
  rw [← h7] at e7
  have st7 : ω7.st = ω6.st := by rw [h7]; simp
  have sh7 : ω7.sh = ω6.sh := by rw [h7]; simp
  have cell7 : ω7.cell = ω6.cell := by rw [h7]; simp
  have val7 : ∀ q, q ≠ fS → ω7.val q = ω6.val q := fun q hq => by rw [h7, wsetv_val_ne _ _ hq]
  have hrb : readTapeBit (ω.st tTW) p2 = decide (rest ≠ []) := by
    have er := ListEval.readTapeBit_drop (ω.st tTW) p2 0
    rw [Nat.add_zero, hd2] at er
    rw [er]
    exact twW_head FP rest (Seams.carLen carriers 0) (Seams.carLen carriers 1)
  have hCnt7 : ∀ (row : Bool) (d : ℕ), CntAt row d 0 0 ω6 → CntAt row d 0 0 ω7 := fun row d hc =>
    ⟨by rw [st7]; exact hc.st, by rw [sh7]; exact hc.sh, by rw [val7 _ (cReg_ne row).2.1]; exact hc.c,
      by rw [val7 _ (cReg_ne row).2.2.2.1]; exact hc.f, by rw [val7 _ (cReg_ne row).2.2.2.2.2]; exact hc.k⟩
  rw [← hsum]
  refine ⟨ω7, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 e7)))))) rfl ?_, ?_, ?_, ?_, ?_⟩
  · unfold sbCost
    rw [← ht0, ← ht1]
    omega
  · obtain ⟨YU, hYU, hlU⟩ := hI6.U
    obtain ⟨YV, hYV, hlV⟩ := hI6.V
    obtain ⟨YC, hYC, hlC⟩ := hI6.C
    refine
      { st := ?_, sh := ?_, val := ?_, cell := ?_, Nw := ?_, U := ⟨YU, ?_, hlU⟩, V := ⟨YV, ?_, hlV⟩,
        C := ⟨YC, ?_, hlC⟩, T := ?_, car := ?_, sc := ?_, cc := hCnt7 false _ hCc6, cr := hCnt7 true _ hCr6 }
    · intro i hk hi0 hi1
      rw [st7, hI6.st i hk, st5 i hi0 hi1]
      exact hI.st i hk hi0 hi1
    · rw [sh7, hI6.sh, sh5]
      exact hI.sh
    · intro q hqP hqF
      rw [val7 q hqF]
      by_cases hc0 : q = cF false
      · rw [hc0, hCc6.f, ← hI.val _ (cReg_ne false).2.2.1 (cReg_ne false).2.2.2.1, hI.cc.f]
      · by_cases hc1 : q = cF true
        · rw [hc1, hCr6.f, ← hI.val _ (cReg_ne true).2.2.1 (cReg_ne true).2.2.2.1, hI.cr.f]
        · rw [hI6.val q hc0 hc1, val5 q hqP hqF]
          exact hI.val q hqP hqF
    · rw [cell7, hI6.cell, cell5]
      exact hI.cell
    · rw [st7]
      exact hI6.Nw
    · rw [st7]; exact hYU
    · rw [st7]; exact hYV
    · rw [st7]; exact hYC
    · intro k
      rw [st7, hI6.st (tT k) (keptC_T k), hTg k, tb, tab_len]
    · intro k hk
      have hc := hI6.car k hk
      exact ⟨by rw [st7]; exact hc.G, by rw [st7]; exact hc.acc, by rw [st7]; exact hc.Z⟩
    · intro i hi b hb
      rw [st7] at hb
      exact hI6.sc i hi b hb
  · rw [val7 _ fS_ne_P.symm, hI6.val _ (cReg_ne false).2.2.1.symm (cReg_ne true).2.2.1.symm]
    exact v5P
  · rw [h7, wsetv_val_self, st6W, hrb]
  · rw [st7, st6W]
    exact hd2

end NearCubicWires.WireExponent3_5.FinalPass.Sd
