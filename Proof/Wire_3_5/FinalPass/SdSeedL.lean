import Proof.Wire_3_5.FinalPass.SdSeedI

/-! # S4 (the seeds phase), part 21: the seed loop (P3:2036-2101, 3044-3048)

**`seedLoop E`**: the first seed's test (`peek`), then `seedBody E` while the flag `fS` is set. **`seedWhile_spec`**
(by induction over the seeds still ahead on the tables word): from `SdInv` at `x`, the loop adds the seeds' terms
`Σ_{e ∈ es} Gs e`, leaves the flag down and the saved position at the tables word's end. **`seedLoop_spec`**: the
same from the loop's entry (position `0`, flag down). `sdInv_setv_fS`: `SdInv` does not see the flag.

Paper quantity of the main type: the sum over the filter seeds `Σ_e Σ_c Σ_ℓ M(e, x_{c,ℓ})·Σ R̂(x_{c,ℓ})`. -/

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

section Lay
variable {nw nn nsc nrs : ℕ}

/-- **`SdInv` does not see the seed flag.** -/
theorem sdInv_setv_fS (FP : GapParams) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (W x : ℕ)
    (ωQ ω : BS nw nn nsc nrs) (v : ℕ) (hI : SdInv FP P carriers W x ωQ ω) :
    SdInv FP P carriers W x ωQ (ω.setv fS v) :=
  { st := hI.st, sh := hI.sh, val := fun q h1 h2 => by rw [wsetv_val_ne _ _ h2]; exact hI.val q h1 h2,
    cell := hI.cell, Nw := hI.Nw, U := hI.U, V := hI.V, C := hI.C, T := hI.T,
    car := fun k hk => ⟨(hI.car k hk).G, (hI.car k hk).acc, (hI.car k hk).Z⟩, sc := hI.sc,
    cc := ⟨hI.cc.st, hI.cc.sh, by rw [wsetv_val_ne _ _ (cReg_ne false).2.1]; exact hI.cc.c,
      by rw [wsetv_val_ne _ _ (cReg_ne false).2.2.2.1]; exact hI.cc.f,
      by rw [wsetv_val_ne _ _ (cReg_ne false).2.2.2.2.2]; exact hI.cc.k⟩,
    cr := ⟨hI.cr.st, hI.cr.sh, by rw [wsetv_val_ne _ _ (cReg_ne true).2.1]; exact hI.cr.c,
      by rw [wsetv_val_ne _ _ (cReg_ne true).2.2.2.1]; exact hI.cr.f,
      by rw [wsetv_val_ne _ _ (cReg_ne true).2.2.2.2.2]; exact hI.cr.k⟩ }

end Lay

variable (E : SymPtEval2)

/-- The seed loop's cost over the seeds `es` still ahead. -/
def slCost (FP : GapParams) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (L s bb h tl nE Vm T Lw : ℕ)
    (es : List (GapSeed FP)) : ℕ :=
  (es.map fun e => sbCost FP e P carriers L s bb h tl nE Vm T Lw + 2).sum + 1

/-- **The seed loop over the seeds ahead.** -/
theorem seedWhile_spec (cap : ℕ) (FP : GapParams) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm Bd : ℕ) (ωQ : BS E.nw E.nn E.nsc E.nrs)
    (H : QHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ωQ) (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T) :
    ∀ (es : List (GapSeed FP)) (x p : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs), SdInv FP P carriers W x ωQ ω →
      ω.val rgP = p → ω.val fS = (decide (es ≠ [])).toNat →
      (ω.st tTW).drop p = twW FP es (Seams.carLen carriers 0) (Seams.carLen carriers 1) →
      x + (es.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum ≤ Bd →
      ∃ ω', WExec cap (.whr fS (seedBody E)) ω ω'
          (slCost FP P carriers ps.length s bb h tl nE Vm T (ωQ.st tTW).length es) ∧
        SdInv FP P carriers W (x + (es.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum) ωQ ω' ∧
        ω'.val fS = 0 ∧
        ω'.val rgP + 1 = p + (twW FP es (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length
  | [], x, p, ω, hI, hP, hF, _, _ => by
    have hF0 : ω.val fS = 0 := by rw [hF]; simp
    refine ⟨ω, WExec.cast cap (WExec.whrF hF0) rfl (by simp [slCost]), by simpa using hI, hF0, ?_⟩
    simp [twW, hP]
  | e :: rest, x, p, ω, hI, hP, hF, hTW, hb => by
    have hF1 : ω.val fS = 1 := by rw [hF]; simp
    have hsum : ((e :: rest).map fun e => Gs FP e P σT carriers ps eu ev Vf).sum =
        Gs FP e P σT carriers ps eu ev Vf + (rest.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum := by
      simp
    rw [hsum] at hb ⊢
    obtain ⟨ω1, e1, hI1, hP1, hF1', hTW1⟩ := seedIter_spec E cap FP P σT carriers ps eu ev Vf s bb h tl W T nE Vm Bd
      ωQ H hBW hBT e rest x p ω hI hP hF1 hTW (by omega)
    obtain ⟨ω', e', hI', hF', hP'⟩ := seedWhile_spec cap FP P σT carriers ps eu ev Vf s bb h tl W T nE Vm Bd ωQ H hBW
      hBT rest (x + Gs FP e P σT carriers ps eu ev Vf) _ ω1 hI1 hP1 hF1' hTW1 (by omega)
    refine ⟨ω', WExec.cast cap (WExec.whrT (by rw [hF1]; omega) e1 e') rfl ?_, ?_, hF', ?_⟩
    · simp only [slCost, List.map_cons, List.sum_cons]
      omega
    · rw [← Nat.add_assoc]
      exact hI'
    · rw [hP', twW_cons]
      simp only [List.length_append, frameP_length, List.length_cons]
      omega

/-- **The seed loop**: the first seed's test, then one seed while the flag is set. -/
noncomputable def seedLoop : BP E.nw E.nn E.nsc E.nrs := .seq peek (.whr fS (seedBody E))

/-- **The seed loop from its entry**: every seed's term added. -/
theorem seedLoop_spec (cap : ℕ) (FP : GapParams) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm Bd : ℕ) (ωQ : BS E.nw E.nn E.nsc E.nrs)
    (H : QHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ωQ) (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T)
    (es : List (GapSeed FP)) (x : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs) (hI : SdInv FP P carriers W x ωQ ω)
    (hP : ω.val rgP = 0) (hF : ω.val fS = 0)
    (hTW : ω.st tTW = twW FP es (Seams.carLen carriers 0) (Seams.carLen carriers 1))
    (hb : x + (es.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum ≤ Bd) :
    ∃ ω', WExec cap (seedLoop E) ω ω' (slCost FP P carriers ps.length s bb h tl nE Vm T (ωQ.st tTW).length es + 9) ∧
      SdInv FP P carriers W (x + (es.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum) ωQ ω' ∧
      ω'.val fS = 0 ∧
      ω'.val rgP + 1 = (twW FP es (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length := by
  have hsh0 : ∀ i, ω.sh i = 0 := fun i => by rw [hI.sh]; exact H.R.sh i
  have hTv : ω.val rgT = 0 := by rw [hI.val _ rgP_ne_T.symm fS_ne_T.symm]; exact H.regT
  have e1 := peek_spec cap 0 ω (hsh0 _) hTv hP hF (by have := H.R.cap2; omega)
  have hrb : readTapeBit (ω.st tTW) 0 = decide (es ≠ []) := by
    rw [hTW]
    exact twW_head FP es (Seams.carLen carriers 0) (Seams.carLen carriers 1)
  rw [hrb] at e1
  obtain ⟨ω', e2, hI', hF', hP'⟩ := seedWhile_spec E cap FP P σT carriers ps eu ev Vf s bb h tl W T nE Vm Bd ωQ H hBW
    hBT es x 0 (ω.setv fS (decide (es ≠ [])).toNat) (sdInv_setv_fS FP P carriers W x ωQ ω _ hI)
    (by rw [wsetv_val_ne _ _ fS_ne_P.symm]; exact hP) (by simp)
    (by simp only [WState.setv_st, List.drop_zero]; exact hTW) hb
  exact ⟨ω', WExec.cast cap (WExec.seq e1 e2) rfl (by omega), hI', hF', by omega⟩

end NearCubicWires.WireExponent3_5.FinalPass.Sd
