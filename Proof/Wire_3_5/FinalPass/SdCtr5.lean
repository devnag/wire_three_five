import Proof.Wire_3_5.FinalPass.SdCtr4

/-! # S4 (the seeds phase), part 14: all the centers (P3:1206-1216, 3044-3048)

The loop over the centers at a filter seed: the rows' counter (`tRow`), inside it the columns' counter (`tCol`), each
by `cntW` (part 11); at every position one center (`cBody`, part 13); each row ends by resetting the columns' word,
the loop by resetting the rows'. `CHyp` bundles the hypotheses (the static facts `CStat`, stage 0's decoding, the
evaluator at every center, the capacities). **`rBody_spec`**: one row adds `rG row = Σ_{col} g row col`;
**`ctrLoop_spec`**: the whole loop adds `Σ_{row} rG row`; **`ctrLoop_sum`**: that is the sum over the cell centers of
the sampled pairs' terms (`sum_centers`).

Paper quantity of the main type: `Σ_{c center} Σ_ℓ M(e, x_{c,ℓ})·Σ R̂(x_{c,ℓ})` at a filter seed. -/

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

/-- **The center loop's hypotheses.** -/
structure CHyp (cap : ℕ) (FP : GapParams) (P : StarParams) (σT : P.Translation) (carriers : List (Stars.Carrier P.n))
    {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n) (Vf : BitInput P.n → Fin N → Fin N → ℕ)
    (s bb h tl T nE Vm : ℕ) (ωR0 : BS E.nw E.nn E.nsc E.nrs) : Prop where
  R : CStat cap FP carriers P σT ps s bb h tl ωR0
  bs : bb + 1 = 2 ^ s
  n : h * bb + h * bb + tl = P.n
  kh : 1 ≤ s * h
  dl : ∀ a : Fin N, decWord bb h tl false (digitsOf s h (binary (s * h) a)) = List.ofFn (eu a)
  dr : ∀ b : Fin N, decWord bb h tl true (digitsOf s h (binary (s * h) b)) = List.ofFn (ev b)
  evl : ∀ (c : BitInput P.n) (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs), PtEnvC c (eu a) (ev b) ωR0 ω₀ →
    ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ nE ∧ EvOut (Vf c a b) ω₀ ω₁
  Vle : ∀ c a b, Vf c a b ≤ Vm
  Vc : Vm ≤ cap
  capT : 2 * T + 2 < cap
  cs : 2 * 2 ^ s ≤ cap ∧ s ≤ cap ∧ 2 * P.n ≤ cap ∧ bb ≤ cap ∧ h ≤ cap ∧ tl ≤ cap
  p : ps.length * (2 * (2 * (s * h) + 1)) ≤ cap
  c8 : 8 * (P.n + 2) ≤ cap
  dT : dR P ≤ T ∧ dRow P ≤ T
  c2 : 2 * dR P + 1 ≤ cap ∧ 2 * dRow P + 1 ≤ cap

/-- The center `(row, col)`'s term. -/
def cG (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation) (carriers : List (Stars.Carrier P.n))
    {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n) (Vf : BitInput P.n → Fin N → Fin N → ℕ)
    (row col : ℕ) : ℕ :=
  sSum FP e carriers (centerAt P σT row col) eu ev (Vf (centerAt P σT row col)) ps

/-- The row's term. -/
def rG (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation) (carriers : List (Stars.Carrier P.n))
    {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n) (Vf : BitInput P.n → Fin N → Fin N → ℕ)
    (row : ℕ) : ℕ :=
  ∑ col ∈ Finset.Ico 0 (2 ^ dR P), cG FP e P σT carriers ps eu ev Vf row col

/-- **One row**: the columns' flag set, the columns' loop, the columns' word reset. -/
noncomputable def rBody : BP E.nw E.nn E.nsc E.nrs := .seq (.inc (cF false)) (.seq (cntW false (cBody E)) (cntRst false))

/-- One row's cost. -/
def rbCost (FP : GapParams) (e : GapSeed FP) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (L s bb h tl nE Vm T : ℕ) :
    ℕ :=
  3 + 1 + ((2 ^ dR P * cntCost (dR P) T (cbCost FP e P carriers L s bb h tl nE Vm T) + 1) + 1 +
    (dR P * 20 + 1 + 1 + (5 * (2 * dR P) + 1)))

theorem rBody_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm Bd : ℕ) (ωR0 : BS E.nw E.nn E.nsc E.nrs)
    (H : CHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ωR0) (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T) :
    ∀ (row a : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs), row < 2 ^ dRow P →
      a + ∑ y ∈ Finset.Ico row (2 ^ dRow P), rG FP e P σT carriers ps eu ev Vf y ≤ Bd →
      (CInvB cap FP e carriers W a ωR0 ω ∧ CntAt false (dR P) 0 0 ω) → CntAt true (dRow P) row 0 ω →
      ∃ ω', WExec cap (rBody E) ω ω' (rbCost FP e P carriers ps.length s bb h tl nE Vm T) ∧
        (CInvB cap FP e carriers W (a + rG FP e P σT carriers ps eu ev Vf row) ωR0 ω' ∧
          CntAt false (dR P) 0 0 ω') ∧ CntAt true (dRow P) row 0 ω' := by
  intro row a ω hrow hBd hJ hCr
  obtain ⟨hI, hC0⟩ := hJ
  have hsum_le : ∀ (f : ℕ → ℕ) (x y z : ℕ), x ≤ y → y < z → f y ≤ ∑ i ∈ Finset.Ico x z, f i := fun f x y z h1 h2 =>
    Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨h1, h2⟩)
  have hrG : rG FP e P σT carriers ps eu ev Vf row ≤ ∑ y ∈ Finset.Ico row (2 ^ dRow P), rG FP e P σT carriers ps eu ev Vf y :=
    hsum_le _ row row _ le_rfl hrow
  -- the columns' flag
  have e1 := WExec.inc (cap := cap) (cF false) ω (by rw [hC0.f]; have := H.R.cap2; omega)
  rw [hC0.f, Nat.zero_add] at e1
  have hne : (cF false : Fin (bnr E.nn E.nrs)) ≠ cF true := by simp only [cF]; apply brg_ne; simp
  -- the columns' loop
  let Jc : ℕ → BS E.nw E.nn E.nsc E.nrs → Prop := fun a' ω' =>
    CInvB cap FP e carriers W a' ωR0 ω' ∧ ω'.st tRow = frame (binary (dRow P) row) ∧ ω'.val (cF true) = 0
  have hTR : (tRow : Fin (bns E.nw E.nsc + 1)) ≠ cT false := by simp only [tRow, cT]; apply bst_ne; simp
  have hJs : ∀ a' (ω' : BS E.nw E.nn E.nsc E.nrs) s', Jc a' ω' → Jc a' (ω'.sets (cT false) s') :=
    fun a' ω' s' h => ⟨cInvB_sets cap FP e carriers W a' ωR0 ω' false s' h.1,
      by simp only [WState.sets_st]; rw [Function.update_of_ne hTR]; exact h.2.1,
      by simp only [WState.sets_val]; exact h.2.2⟩
  have hJv : ∀ a' (ω' : BS E.nw E.nn E.nsc E.nrs) v, Jc a' ω' → Jc a' (ω'.setv (cF false) v) :=
    fun a' ω' v h => ⟨cInvB_setv cap FP e carriers W a' ωR0 ω' false v h.1, h.2.1,
      by rw [wsetv_val_ne _ _ hne.symm]; exact h.2.2⟩
  have hBc : ∀ col a' (ω' : BS E.nw E.nn E.nsc E.nrs), col < 2 ^ dR P →
      a' + ∑ y ∈ Finset.Ico col (2 ^ dR P), cG FP e P σT carriers ps eu ev Vf row y ≤
        a + ∑ y ∈ Finset.Ico 0 (2 ^ dR P), cG FP e P σT carriers ps eu ev Vf row y →
      Jc a' ω' → CntAt false (dR P) col 0 ω' →
      ∃ ω'', WExec cap (cBody E) ω' ω'' (cbCost FP e P carriers ps.length s bb h tl nE Vm T) ∧
        Jc (a' + cG FP e P σT carriers ps eu ev Vf row col) ω'' ∧ CntAt false (dR P) col 0 ω'' := by
    intro col a' ω' hcol hb hJ' hC'
    have h1 := hsum_le (cG FP e P σT carriers ps eu ev Vf row) col col _ le_rfl hcol
    have h2 : a + ∑ y ∈ Finset.Ico 0 (2 ^ dR P), cG FP e P σT carriers ps eu ev Vf row y ≤ Bd := by
      have : ∑ y ∈ Finset.Ico 0 (2 ^ dR P), cG FP e P σT carriers ps eu ev Vf row y =
        rG FP e P σT carriers ps eu ev Vf row := rfl
      omega
    obtain ⟨ω'', e'', hI'', hr'', hc'', hf''⟩ := cBody_spec E cap FP e P σT carriers ps eu ev Vf s bb h tl W T nE Vm ωR0
      H.R H.bs H.n H.kh H.dl H.dr H.evl H.Vle H.Vc H.capT H.cs H.p H.c8 row col a' ω' hJ'.1 hJ'.2.1 hC'.st
      (by show a' + cG FP e P σT carriers ps eu ev Vf row col < 2 ^ W; omega)
      (by show a' + cG FP e P σT carriers ps eu ev Vf row col < 2 ^ T; omega)
    have hsh'' : ∀ i, ω''.sh i = 0 := fun i => by rw [hI''.sh]; exact H.R.sh i
    refine ⟨ω'', e'', ⟨hI'', by rw [hr'']; exact hJ'.2.1, by rw [hf'']; exact hJ'.2.2⟩,
      ⟨by rw [show (cT false : Fin (bns E.nw E.nsc + 1)) = tCol from rfl, hc'']; exact hC'.st, hsh'' _, ?_,
        by rw [hf'']; exact hC'.f, ?_⟩⟩
    · rw [hI''.val _ (by simp only [cC, cF]; apply brg_ne; simp) (by simp only [cC, cF]; apply brg_ne; simp)]
      exact (H.R.cnt false).1
    · rw [hI''.val _ (by simp only [cK, cF]; apply brg_ne; simp) (by simp only [cK, cF]; apply brg_ne; simp)]
      exact (H.R.cnt false).2
  obtain ⟨ω2, e2, hJ2, hC2⟩ := cntW_spec cap false (dR P) T (cbCost FP e P carriers ps.length s bb h tl nE Vm T)
    (a + ∑ y ∈ Finset.Ico 0 (2 ^ dR P), cG FP e P σT carriers ps eu ev Vf row y) (cBody E) Jc
    (cG FP e P σT carriers ps eu ev Vf row) hJs hJv hBc H.dT.1 H.capT H.c2.1 (2 ^ dR P) 0 a
    (ω.setv (cF false) 1) (by omega) Nat.one_le_two_pow le_rfl
    ⟨cInvB_setv cap FP e carriers W a ωR0 ω false 1 hI, by rw [WState.setv_st]; exact hCr.st,
      by rw [wsetv_val_ne _ _ hne.symm]; exact hCr.f⟩
    (cntAt_setF false (dR P) 0 0 1 ω hC0)
  -- the columns' word reset
  have e3 := cnt_rst cap false (dR P) (2 ^ dR P - 1) ω2 hC2.st hC2.sh hC2.c H.c2.1
  have hshR : ∀ i, ω2.sh i = 0 := fun i => by rw [hJ2.1.sh]; exact H.R.sh i
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ⟨cInvB_sets cap FP e carriers W _ ωR0 ω2 false _ hJ2.1,
    ⟨by simp, by simp only [WState.sets_sh]; exact hC2.sh, by simp only [WState.sets_val]; exact hC2.c,
      by simp only [WState.sets_val]; exact hC2.f, by simp only [WState.sets_val]; exact hC2.k⟩⟩,
    ⟨by simp only [WState.sets_st]; rw [show (cT true : Fin (bns E.nw E.nsc + 1)) = tRow from rfl,
        Function.update_of_ne hTR]; exact hJ2.2.1,
      by simp only [WState.sets_sh]; exact hshR _,
      by simp only [WState.sets_val]
         rw [hJ2.1.val _ (by simp only [cC, cF]; apply brg_ne; simp) (by simp only [cC, cF]; apply brg_ne; simp)]
         exact (H.R.cnt true).1,
      by simp only [WState.sets_val]; exact hJ2.2.2,
      by simp only [WState.sets_val]
         rw [hJ2.1.val _ (by simp only [cK, cF]; apply brg_ne; simp) (by simp only [cK, cF]; apply brg_ne; simp)]
         exact (H.R.cnt true).2⟩⟩

/-- **All the centers**: the rows' flag set, the rows' loop, the rows' word reset. -/
noncomputable def ctrLoop : BP E.nw E.nn E.nsc E.nrs := .seq (.inc (cF true)) (.seq (cntW true (rBody E)) (cntRst true))

/-- The center loop's cost. -/
def clCost (FP : GapParams) (e : GapSeed FP) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (L s bb h tl nE Vm T : ℕ) :
    ℕ :=
  3 + 1 + ((2 ^ dRow P * cntCost (dRow P) T (rbCost FP e P carriers L s bb h tl nE Vm T) + 1) + 1 +
    (dRow P * 20 + 1 + 1 + (5 * (2 * dRow P) + 1)))

theorem ctrLoop_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm Bd : ℕ) (ωR0 : BS E.nw E.nn E.nsc E.nrs)
    (H : CHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ωR0) (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T)
    (a : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs) (hI : CInvB cap FP e carriers W a ωR0 ω)
    (hCc : CntAt false (dR P) 0 0 ω) (hCr : CntAt true (dRow P) 0 0 ω)
    (hb : a + ∑ y ∈ Finset.Ico 0 (2 ^ dRow P), rG FP e P σT carriers ps eu ev Vf y ≤ Bd) :
    ∃ ω', WExec cap (ctrLoop E) ω ω' (clCost FP e P carriers ps.length s bb h tl nE Vm T) ∧
      CInvB cap FP e carriers W (a + ∑ y ∈ Finset.Ico 0 (2 ^ dRow P), rG FP e P σT carriers ps eu ev Vf y) ωR0 ω' ∧
      CntAt false (dR P) 0 0 ω' ∧ CntAt true (dRow P) 0 0 ω' := by
  have e1 := WExec.inc (cap := cap) (cF true) ω (by rw [hCr.f]; have := H.R.cap2; omega)
  rw [hCr.f, Nat.zero_add] at e1
  have hTR : (tCol : Fin (bns E.nw E.nsc + 1)) ≠ cT true := by simp only [tCol, cT]; apply bst_ne; simp
  let Jr : ℕ → BS E.nw E.nn E.nsc E.nrs → Prop := fun a' ω' =>
    CInvB cap FP e carriers W a' ωR0 ω' ∧ CntAt false (dR P) 0 0 ω'
  have hJs : ∀ a' (ω' : BS E.nw E.nn E.nsc E.nrs) s', Jr a' ω' → Jr a' (ω'.sets (cT true) s') :=
    fun a' ω' s' h => ⟨cInvB_sets cap FP e carriers W a' ωR0 ω' true s' h.1,
      ⟨by simp only [WState.sets_st]; rw [show (cT false : Fin (bns E.nw E.nsc + 1)) = tCol from rfl,
          Function.update_of_ne hTR]; exact h.2.st,
        by simp only [WState.sets_sh]; exact h.2.sh, by simp only [WState.sets_val]; exact h.2.c,
        by simp only [WState.sets_val]; exact h.2.f, by simp only [WState.sets_val]; exact h.2.k⟩⟩
  have hJv : ∀ a' (ω' : BS E.nw E.nn E.nsc E.nrs) v, Jr a' ω' → Jr a' (ω'.setv (cF true) v) :=
    fun a' ω' v h => ⟨cInvB_setv cap FP e carriers W a' ωR0 ω' true v h.1,
      ⟨h.2.st, h.2.sh,
        by rw [wsetv_val_ne _ _ (show (cC false : Fin (bnr E.nn E.nrs)) ≠ cF true by
          simp only [cC, cF]; apply brg_ne; simp)]; exact h.2.c,
        by rw [wsetv_val_ne _ _ (show (cF false : Fin (bnr E.nn E.nrs)) ≠ cF true by
          simp only [cF]; apply brg_ne; simp)]; exact h.2.f,
        by rw [wsetv_val_ne _ _ (show (cK false : Fin (bnr E.nn E.nrs)) ≠ cF true by
          simp only [cK, cF]; apply brg_ne; simp)]; exact h.2.k⟩⟩
  obtain ⟨ω2, e2, hJ2, hC2⟩ := cntW_spec cap true (dRow P) T (rbCost FP e P carriers ps.length s bb h tl nE Vm T) Bd
    (rBody E) Jr (rG FP e P σT carriers ps eu ev Vf) hJs hJv
    (rBody_spec E cap FP e P σT carriers ps eu ev Vf s bb h tl W T nE Vm Bd ωR0 H hBW hBT)
    H.dT.2 H.capT H.c2.2 (2 ^ dRow P) 0 a (ω.setv (cF true) 1) (by omega) Nat.one_le_two_pow hb
    (hJv a ω 1 ⟨hI, hCc⟩) (cntAt_setF true (dRow P) 0 0 1 ω hCr)
  have e3 := cnt_rst cap true (dRow P) (2 ^ dRow P - 1) ω2 hC2.st hC2.sh hC2.c H.c2.2
  have hJ3 := hJs _ ω2 (frame (binary (dRow P) 0)) hJ2
  exact ⟨_, WExec.seq e1 (WExec.seq e2 e3), hJ3.1, hJ3.2,
    ⟨by simp, by simp only [WState.sets_sh]; exact hC2.sh, by simp only [WState.sets_val]; exact hC2.c,
      by simp only [WState.sets_val]; exact hC2.f, by simp only [WState.sets_val]; exact hC2.k⟩⟩

/-- **The loop's sum is the sum over the cell centers** (`sum_centers`). -/
theorem ctrLoop_sum (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) :
    ∑ y ∈ Finset.Ico 0 (2 ^ dRow P), rG FP e P σT carriers ps eu ev Vf y =
      ∑ c : {c // P.IsCenter σT c}, sSum FP e carriers c.1 eu ev (Vf c.1) ps := by
  rw [PrimT.Ctr.sum_centers P σT (fun c => sSum FP e carriers c eu ev (Vf c) ps)]
  simp only [rG, cG, Finset.range_eq_Ico]

end NearCubicWires.WireExponent3_5.FinalPass.Sd
