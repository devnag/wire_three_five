import Proof.Wire_3_5.UnionMachine.FrontC1D
import Proof.Wire_3_5.UnionMachine.FrontAtP
import Proof.Wire_3_5.UnionMachine.FrontEnd
import Proof.Wire_3_5.UnionMachine.FrontPh1

/-! # C6 front, the chain after phase 2 at one class mode (P3:3669-3680, 3092-3094, 3409-3410, 3673, 3485-3491)

At the guess's class mode `m`, the rest of the front: a copy of `frame x`, phase 3 (the counts, the request head, the
numbers, the entries' verdict), a branch on the entries (else the rejecting bank), the atom test, a branch on its
verdict (`0`: go on; else the rejecting bank), phase 5 (the table writer's sources), C1's call (the selected coset),
and the front's end (the table writer, `OK`, the loop bank or the rejecting bank). **`restM`**; its layout `RS`.

Paper quantity of the main type: the front's output bank at one class mode. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontRest
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3 NearCubicWires.WireExponent3_5.UnionMachine.FrontCh5

section CopyX
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- **The copy of `frame x`** (the input tape `0`, base's witness copy) into a region: `frame x` on its tape `1`. -/
theorem frStageX (xs : List Bool) (k : ℕ) (hk : k + 4 ≤ tf) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k) (hx : A (FrontPh1.xT P tf) = frame xs ∧ H (FrontPh1.xT P tf) = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk) RecoveryColdWitnessCopy.machine)
        (8 * xs.length + 14) H A H A' ∧
      A' (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk (1 : Fin 4)) = frame xs ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k → A' y = A y) ∧ PristineH P tf H A' (k + 4) := by
  have x0 : (FrontPh1.xT P tf).val = 0 := rfl
  have hlow : ∀ i a, sh1 (t := 4) P tf (FrontPh1.xT P tf) i = some a → a.val < 2 + NL P + k := fun i a hi => by
    unfold sh1 at hi; split_ifs at hi; rw [← Option.some.inj hi, x0]; omega
  have hshL : ∀ i a, sh1 (t := 4) P tf (FrontPh1.xT P tf) i = some a → 2 + NL P ≤ a.val ∨ a.val < 2 :=
    fun i a hi => by unfold sh1 at hi; split_ifs at hi; rw [← Option.some.inj hi, x0]; omega
  have hinj := sl_inj P tf _ k hk (sh1_I P tf _) hlow
  have e0 : sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk (0 : Fin 4) = FrontPh1.xT P tf :=
    sl_some P tf _ k hk 0 _ (sh1_zero P tf _ 0 rfl)
  have hH0 : ∀ j, H (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk j) = 0 := by
    intro j
    by_cases h0 : j.val = 0
    · rw [sl_some P tf _ k hk j _ (sh1_zero P tf _ j h0)]; exact hx.2
    · rw [sl_none P tf _ k hk j (sh1_ne P tf _ j h0)]; exact (hPr.1 _ (by rw [rg_val]; omega)).2
  have hA0 : ∀ j, A (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk j) = RecoveryColdWitnessCopy.input xs j := by
    intro j
    by_cases h0 : j.val = 0
    · rw [sl_some P tf _ k hk j _ (sh1_zero P tf _ j h0), hx.1, show j = 0 from Fin.ext h0]; rfl
    · rw [sl_none P tf _ k hk j (sh1_ne P tf _ j h0), (hPr.1 _ (by rw [rg_val]; omega)).1]
      fin_cases j <;> simp_all [RecoveryColdWitnessCopy.input]
  have st := dockAny (step_of_rready (RecoveryColdWitnessCopy.copy_ready xs)) _ hinj H A hH0 hA0
  have hpr := pristineH_after P tf _ k hk hlow hshL H A (fun _ => 0) (RecoveryColdWitnessCopy.output xs) hPr
  rw [ExtDecompositionBatch.dockH_existing _ H _ hH0] at st hpr
  refine ⟨_, st, install_slot _ hinj _ _ _, fun y hy => ?_, hpr⟩
  by_cases hyx : y = FrontPh1.xT P tf
  · subst hyx
    calc install (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk) A (RecoveryColdWitnessCopy.output xs) (FrontPh1.xT P tf)
        = install (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk) A (RecoveryColdWitnessCopy.output xs)
            (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k hk 0) := by rw [e0]
      _ = RecoveryColdWitnessCopy.output xs 0 := install_slot _ hinj _ _ _
      _ = A (FrontPh1.xT P tf) := by rw [hx.1]; rfl
  · exact install_low P tf _ k hk A _ y hy (fun i a hi e => by
      unfold sh1 at hi; split_ifs at hi; rw [← Option.some.inj hi] at e; exact hyx e.symm)

end CopyX

/-! ## The table writer's source map -/

/-- Ten tapes as the table writer's streams `1 … 10`. -/
def srcX {N : ℕ} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Fin N) (i : Fin 10) : Fin N :=
  if i.val = 0 then a0 else if i.val = 1 then a1 else if i.val = 2 then a2 else if i.val = 3 then a3
  else if i.val = 4 then a4 else if i.val = 5 then a5 else if i.val = 6 then a6 else if i.val = 7 then a7
  else if i.val = 8 then a8 else a9

/-- The table writer's sources on the valid path (streams `1 … 10`). -/
def srcV (po rw hd tl cc pc cr : List Bool) (E nv : ℕ) (ef : List Bool) (i : Fin 10) : List Bool :=
  if i.val = 0 then po else if i.val = 1 then rw else if i.val = 2 then hd else if i.val = 3 then tl
  else if i.val = 4 then cc else if i.val = 5 then pc else if i.val = 6 then cr
  else if i.val = 7 then List.replicate E true else if i.val = 8 then List.replicate nv true else ef

theorem srcs_of {N : ℕ} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Fin N) (A : Fin N → List Bool) (H : Fin N → ℕ)
    (po rw hd tl cc pc cr : List Bool) (E nv : ℕ) (ef : List Bool)
    (g0 : A a0 = po ∧ H a0 = 0) (g1 : A a1 = rw ∧ H a1 = 0) (g2 : A a2 = hd ∧ H a2 = 0) (g3 : A a3 = tl ∧ H a3 = 0)
    (g4 : A a4 = cc ∧ H a4 = 0) (g5 : A a5 = pc ∧ H a5 = 0) (g6 : A a6 = cr ∧ H a6 = 0)
    (g7 : A a7 = List.replicate E true ∧ H a7 = 0) (g8 : A a8 = List.replicate nv true ∧ H a8 = 0)
    (g9 : A a9 = ef ∧ H a9 = 0) :
    ∀ i : Fin 10, A (srcX a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 i) = srcV po rw hd tl cc pc cr E nv ef i ∧
      H (srcX a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 i) = 0 := by
  intro i
  obtain ⟨v, hv⟩ := i
  unfold srcX srcV
  simp only [Fin.val_mk]
  interval_cases v <;> simp only [if_true, if_false, OfNat.ofNat_ne_zero, one_ne_zero] <;> first
    | exact g0 | exact g1 | exact g2 | exact g3 | exact g4 | exact g5 | exact g6 | exact g7 | exact g8 | exact g9
    | simp_all

/-! ## The layout -/

section Layout
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)

/-- The chain's size after phase 2 at mode `m`. -/
noncomputable abbrev RS : ℕ :=
  4 + FrontCh3P.CH3 Dw Dl + FrontAtP.AP + CH5 m deg De Dt + FrontC1D.C1P c + WT 11 56 + WT 25 105

/-- The regions' offsets. -/
noncomputable abbrev oA (k0 : ℕ) : ℕ := k0 + 4 + FrontCh3P.CH3 Dw Dl
noncomputable abbrev o5 (k0 : ℕ) : ℕ := oA Dw Dl k0 + FrontAtP.AP
noncomputable abbrev oC (k0 : ℕ) : ℕ := o5 Dw Dl k0 + CH5 m deg De Dt
noncomputable abbrev oE (k0 : ℕ) : ℕ := oC m Dw Dl deg De Dt k0 + FrontC1D.C1P c
noncomputable abbrev oT (k0 : ℕ) : ℕ := oE m Dw Dl deg De Dt c k0 + WT 11 56

variable (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)

include h in
theorem hr1 : k0 + 4 ≤ tf := by unfold RS at h; omega
include h in
theorem hr2 : (k0 + 4) + FrontCh3P.CH3 Dw Dl ≤ tf := by unfold RS at h; omega
include h in
theorem hr3 : oA Dw Dl k0 + FrontAtP.AP ≤ tf := by unfold RS at h; unfold oA; omega
include h in
theorem hr4 : o5 Dw Dl k0 + CH5 m deg De Dt ≤ tf := by unfold RS at h; unfold o5 oA; omega
include h in
theorem hr5 : oC m Dw Dl deg De Dt k0 + FrontC1D.C1P c ≤ tf := by unfold RS at h; unfold oC o5 oA; omega
include h in
theorem hr6 : oE m Dw Dl deg De Dt c k0 + WT 11 56 ≤ tf := by unfold RS at h; unfold oE oC o5 oA; omega
include h in
theorem hr7 : oT m Dw Dl deg De Dt c k0 + WT 25 105 ≤ tf := by unfold RS at h; unfold oT oE oC o5 oA; omega

variable (qT rT poT : Fin (NW P tf))

/-- The copy of `frame x`. -/
noncomputable def cxR : Fin (NW P tf) :=
  sl P tf (sh1 P tf (FrontPh1.xT P tf)) k0 (hr1 tf m Dw Dl deg De Dt c k0 h) (1 : Fin 4)

/-- Phase 3's tapes. -/
noncomputable def wcR : Fin (NW P tf) := FrontCh3P.wcT P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT
noncomputable def lcR : Fin (NW P tf) := FrontCh3P.lcT P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT
noncomputable def x1R : Fin (NW P tf) :=
  FrontCh3P.x1T P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) (cxR P tf m Dw Dl deg De Dt c k0 h)
noncomputable def x2R : Fin (NW P tf) :=
  FrontCh3P.x2T P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) (cxR P tf m Dw Dl deg De Dt c k0 h)
noncomputable def hdR : Fin (NW P tf) := FrontCh3P.hdT P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT
noncomputable def nuR (i : Fin 11) : Fin (NW P tf) :=
  FrontCh3P.nuT P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT poT i
noncomputable def ecR : Fin (NW P tf) :=
  FrontCh3P.ecT P tf Dw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT (cxR P tf m Dw Dl deg De Dt c k0 h) rT poT

/-- The atom test's verdict. -/
noncomputable def vtR : Fin (NW P tf) :=
  FrontAtP.vtT P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT (x1R P tf m Dw Dl deg De Dt c k0 h)
    qT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) (x2R P tf m Dw Dl deg De Dt c k0 h)
    (lcR P tf m Dw Dl deg De Dt c k0 h qT)

/-- Phase 5's outputs. -/
noncomputable def unR : Fin (NW P tf) :=
  unT P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT (wcR P tf m Dw Dl deg De Dt c k0 h qT)
noncomputable def ccR : Fin (NW P tf) := ccO P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h)
noncomputable def fiR (j : ℕ) (hj : j < 10) : Fin (NW P tf) :=
  fiT P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT (wcR P tf m Dw Dl deg De Dt c k0 h qT)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7) (wcR P tf m Dw Dl deg De Dt c k0 h qT) j hj

/-- C1's framed coset. -/
noncomputable def c1R : Fin (NW P tf) :=
  FrontC1D.c1O P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6)

/-- The table writer's sources (streams `1 … 10`): the PCPP output, the raw rest, the request head, the coset, the
constant's code, the parity codes, the carrier codes, `1^E` (the atoms' flags), `1^{nv}` (the parities' flags), the
envelope bits. -/
noncomputable def srcR : Fin 10 → Fin (NW P tf) :=
  srcX poT (unR P tf m Dw Dl deg De Dt c k0 h qT rT) (hdR P tf m Dw Dl deg De Dt c k0 h qT)
    (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT) (ccR P tf m Dw Dl deg De Dt c k0 h)
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)) (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num))
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6)
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num))

/-- **The chain after phase 2 at mode `m`.** -/
noncomputable def restM (Kw : ℕ) (Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k0 (hr1 tf m Dw Dl deg De Dt c k0 h))
    RecoveryColdWitnessCopy.machine)
  (Composition.machine (FrontCh3P.ch3M P tf Dw Kw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT
      (cxR P tf m Dw Dl deg De Dt c k0 h) rT poT (FrontTW.modeBit m) Kb Db cdf ζ Cδ)
  (iteMachine (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT)
    (Composition.machine (FrontAtP.atM P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT
        (x1R P tf m Dw Dl deg De Dt c k0 h) qT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0)
        (x2R P tf m Dw Dl deg De Dt c k0 h) (lcR P tf m Dw Dl deg De Dt c k0 h qT) m)
      (iteMachine (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT) (FrontGate.rejM P tf)
        (Composition.machine (ch5M P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) Ce Ct)
        (Composition.machine (FrontC1D.c1M P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
            (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) cr)
          (FrontEnd.endM P tf Pw crT KT AT (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (oE m Dw Dl deg De Dt c k0) (hr6 tf m Dw Dl deg De Dt c k0 h)
            (oT m Dw Dl deg De Dt c k0) (hr7 tf m Dw Dl deg De Dt c k0 h))))))
    (FrontGate.rejM P tf)))

end Layout

/-! ## The runs -/

section Runs
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord)

theorem cxR_val : (cxR P tf m Dw Dl deg De Dt c k0 h).val = 2 + NL P + (k0 + 1) := by
  unfold cxR; rw [sl_none P tf _ _ _ _ (sh1_ne P tf _ _ (by decide)), rg_val]; rfl

theorem ecR_ge : 2 + NL P + (k0 + 4) ≤ (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT).val := by
  unfold ecR FrontCh3P.ecT
  rw [sl_none P tf _ _ _ _ (by unfold FrontCh3P.insE; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]),
    rg_val]
  omega

/-- **The copy of `x` and phase 3** on the chain's first regions. -/
theorem rest_pre (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db : ℕ) (cdf : Bool) (Cδ : ℕ)
    (q sys aux cb : ℕ) (x r restP : List Bool) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0)
    (hX : A (FrontPh1.xT P tf) = frame x ∧ H (FrontPh1.xT P tf) = 0) (hq : A qT = List.replicate q true ∧ H qT = 0)
    (hR : A rT = frame r ∧ H rT = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hx : r.length + 1 ≤ x.length) (hN : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb) :
    ∃ A0 A1 : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k0 (hr1 tf m Dw Dl deg De Dt c k0 h))
        RecoveryColdWitnessCopy.machine) (8 * x.length + 14) H A H A0 ∧
      Step (FrontCh3P.ch3M P tf Dw Kw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT (cxR P tf m Dw Dl deg De Dt c k0 h)
        rT poT (FrontTW.modeBit m) Kb Db cdf ζ Cδ) (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r)
        H A0 H A1 ∧
      A1 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate (Kw * (q + 1) ^ Dw) true ∧
      A1 (lcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate ((q + 1) ^ Dl) true ∧
      A1 (x1R P tf m Dw Dl deg De Dt c k0 h) = List.replicate x.length true ∧
      A1 (x2R P tf m Dw Dl deg De Dt c k0 h) = List.replicate x.length true ∧
      A1 (hdR P tf m Dw Dl deg De Dt c k0 h qT) = frame (natWord q ++ [FrontTW.modeBit m] ++ natWord 4) ∧
      A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) =
        List.replicate ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2) = List.replicate (Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) = List.replicate sys true ∧
      A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5) = List.replicate aux true ∧
      A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) = List.replicate (sys + aux) true ∧
      A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7) = false :: List.replicate (sys + aux) true ∧
      A1 (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT) =
        [(FrontEntriesRef.entScan ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) r).isSome] ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A1 y = A y) ∧
      PristineH P tf H A1 (oA Dw Dl k0) := by
  have vX := cxR_val P tf m Dw Dl deg De Dt c k0 h
  obtain ⟨A0, s0, w0, l0, p0⟩ := frStageX P tf x k0 (hr1 tf m Dw Dl deg De Dt c k0 h) H A hPr hX
  obtain ⟨A1, s1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, l1, p1⟩ :=
    FrontCh3P.ch3_step P tf Dw Kw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT (cxR P tf m Dw Dl deg De Dt c k0 h)
      rT poT h0 h1 (FrontTW.modeBit m) Kb Db cdf Cδ q sys aux cb x r restP H A0 p0 ⟨hqL.1, by omega⟩
      ⟨by omega, by omega⟩ ⟨hrL.1, by omega⟩ ⟨hpL.1, by omega⟩
      (fun e => by have := congrArg Fin.val e; rw [vX] at this; omega)
      ⟨by rw [l0 qT hqL.2]; exact hq.1, hq.2⟩ ⟨w0, (hPr.1 _ (by omega)).2⟩ ⟨by rw [l0 rT hrL.2]; exact hR.1, hR.2⟩
      ⟨by rw [l0 poT hpL.2]; exact hp.1, hp.2⟩ hx hN
  exact ⟨A0, A1, s0, s1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
    fun y hy => by rw [l1 y (by omega), l0 y hy], p1⟩

end Runs

/-! ## The rejecting branches -/

section Rej
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord)

/-- **The entries fail**: the rejecting bank. -/
theorem rest_rejE (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db : ℕ) (cdf : Bool) (Cδ Ce Ct cr : ℕ)
    (Pw : WM 10 56) (crT KT AT : ℕ)
    (q sys aux cb : ℕ) (x r restP : List Bool) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0)
    (hX : A (FrontPh1.xT P tf) = frame x ∧ H (FrontPh1.xT P tf) = 0) (hq : A qT = List.replicate q true ∧ H qT = 0)
    (hR : A rT = frame r ∧ H rT = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hx : r.length + 1 ≤ x.length)
    (hN : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (hE : (FrontEntriesRef.entScan ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) r).isSome = false) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (restM P tf m Dw Dl deg De Dt c k0 h qT rT poT Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        ((8 * x.length + 14) + 1 + (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r + 1 + (3 + 1)))
        H A H' A' ∧
      (∀ i, H' (lp P tf i) = bankH P FrontGate.rejKept i) ∧ (∀ i, A' (lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨A0, A1, s0, s1, -, -, -, -, -, -, -, -, -, -, -, ec, -, p1⟩ := rest_pre P tf m Dw Dl deg De Dt c k0 h qT rT poT
    Kw h0 h1 Kb Db cdf Cδ q sys aux cb x r restP H A hPr hqL hrL hpL hX hq hR hp hx hN
  obtain ⟨H2, A2, s2, hH2, hA2, -⟩ := FrontGate.rej_step P tf H A1 (fun i => (p1.2 i).2) (fun i => (p1.2 i).1)
  have hb : readTapeBit (A1 (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT))
      (H (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) = false := by
    have ge := ecR_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT
    rw [ec, (hPr.1 _ (by omega)).2, hE]; rfl
  exact ⟨H2, A2, Step.seq s0 (Step.seq s1 (iteF _ _ _ hb s2)), hH2, hA2⟩

theorem x12R_vals :
    (x1R P tf m Dw Dl deg De Dt c k0 h).val = 2 + NL P + ((k0 + 4 + FrontCh3P.tP Dw + FrontCh3P.tP Dl) + 2) ∧
    (x2R P tf m Dw Dl deg De Dt c k0 h).val = 2 + NL P + ((k0 + 4 + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8) + 2) ∧
    (lcR P tf m Dw Dl deg De Dt c k0 h qT).val = 2 + NL P + ((k0 + 4 + FrontCh3P.tP Dw) + (3 + 2 * Dl)) ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val =
      2 + NL P + (k0 + 4 + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 0) :=
  ⟨FrontCh3P.x1T_val P tf Dw Dl (k0 + 4) _ _, FrontCh3P.x2T_val P tf Dw Dl (k0 + 4) _ _,
    FrontCh3P.lcT_val P tf Dw Dl (k0 + 4) _ _, FrontCh3P.nuT0_val P tf Dw Dl (k0 + 4) _ _ _⟩

theorem ch3_lt : (k0 + 4 + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + WT 10 56) + FrontEntriesStage.ET =
    oA Dw Dl k0 := by
  unfold oA FrontCh3P.CH3; omega

/-- **The atom test fails** (verdict `≠ 0`): the rejecting bank. -/
theorem rest_rejA (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db : ℕ) (cdf : Bool) (Cδ Ce Ct cr : ℕ)
    (Pw : WM 10 56) (crT KT AT : ℕ)
    (q sys aux cb : ℕ) (x r restP : List Bool) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (Kc Kd : ℕ)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0)
    (hX : A (FrontPh1.xT P tf) = frame x ∧ H (FrontPh1.xT P tf) = 0) (hq : A qT = List.replicate q true ∧ H qT = 0)
    (hR : A rT = frame r ∧ H rT = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hx : r.length + 1 ≤ x.length)
    (hN : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (hE : (FrontEntriesRef.entScan ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) r).isSome = true)
    (hA : FrontAtP.AtomsOK r x.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length pos pay Kc Kd)
    (hv : FrontAtomLoop.verdictOf q (FrontAtomStageL.capP x.length) ((q + 1) ^ Dl) m
      ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) pay ≠ 0) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (restM P tf m Dw Dl deg De Dt c k0 h qT rT poT Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        ((8 * x.length + 14) + 1 + (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r + 1 +
          ((FrontAtP.atCost m r x.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length ((q + 1) ^ Dl) Kc Kd
            pay + 1 + (3 + 1)) + 1)))
        H A H' A' ∧
      (∀ i, H' (lp P tf i) = bankH P FrontGate.rejKept i) ∧ (∀ i, A' (lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨A0, A1, s0, s1, e1, e2, e3, e4, -, e6, -, -, -, -, -, ec, l1, p1⟩ := rest_pre P tf m Dw Dl deg De Dt c k0 h
    qT rT poT Kw h0 h1 Kb Db cdf Cδ q sys aux cb x r restP H A hPr hqL hrL hpL hX hq hR hp hx hN
  obtain ⟨v1, v2, vl, v0⟩ := x12R_vals P tf m Dw Dl deg De Dt c k0 h qT poT
  have t1 := FrontCh3P.tP_eq Dw
  have t2 := FrontCh3P.tP_eq Dl
  have hW1 : WT 1 9 = 15 := rfl
  have hoA := ch3_lt Dw Dl k0
  have hWT2 : WT 10 56 = 71 := rfl
  have hET : FrontEntriesStage.ET = 22 := rfl
  obtain ⟨H2, A2, s2, a2, b2, -, p2⟩ := FrontAtP.atP_step P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT
    (x1R P tf m Dw Dl deg De Dt c k0 h) qT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0)
    (x2R P tf m Dw Dl deg De Dt c k0 h) (lcR P tf m Dw Dl deg De Dt c k0 h qT) m r x.length q
    ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length ((q + 1) ^ Dl) pos pay Kc Kd hA H A1 p1
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hrL.1, by omega⟩
      · rw [v1]; constructor <;> omega
      · exact ⟨hqL.1, by omega⟩
      · rw [v0]; constructor <;> omega
      · rw [v2]; constructor <;> omega
      · rw [vl]; constructor <;> omega)
    (fun e => by have := congrArg Fin.val e; rw [v1, v2] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [v1, vl] at this; omega)
    (fun e => by have := congrArg Fin.val e; rw [v2, vl] at this; omega)
    ⟨by rw [l1 rT hrL.2]; exact hR.1, hR.2⟩ ⟨e3, (hPr.1 _ (by rw [v1]; omega)).2⟩
    ⟨by rw [l1 qT hqL.2]; exact hq.1, hq.2⟩ ⟨e6, (hPr.1 _ (by rw [v0]; omega)).2⟩
    ⟨e4, (hPr.1 _ (by rw [v2]; omega)).2⟩ ⟨e2, (hPr.1 _ (by rw [vl]; omega)).2⟩
  obtain ⟨H3, A3, s3, hH3, hA3, -⟩ := FrontGate.rej_step P tf H2 A2 (fun i => (p2.2 i).2) (fun i => (p2.2 i).1)
  have hb1 : readTapeBit (A1 (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT))
      (H (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) = true := by
    have ge := ecR_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT
    rw [ec, (hPr.1 _ (by omega)).2, hE]; rfl
  have hb2 : readTapeBit (A2 (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT))
      (H2 (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) = true := by
    unfold vtR; rw [a2, b2, regTape_read]; simp [hv]
  refine ⟨H3, A3, ?_, hH3, hA3⟩
  unfold restM
  refine Step.seq s0 (Step.seq s1 (iteT _ _ _ hb1 ?_))
  have s4 := iteT (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT) (FrontGate.rejM P tf)
    (Composition.machine (ch5M P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) Ce Ct)
        (Composition.machine (FrontC1D.c1M P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
            (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) cr)
          (FrontEnd.endM P tf Pw crT KT AT (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (oE m Dw Dl deg De Dt c k0) (hr6 tf m Dw Dl deg De Dt c k0 h)
            (oT m Dw Dl deg De Dt c k0) (hr7 tf m Dw Dl deg De Dt c k0 h)))) hb2 s3
  have s5 := Step.seq s2 s4
  exact s5

end Rej

/-! ## The valid path, stage by stage -/

section PathStages
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-- Phase 3's tapes the later stages read. -/
noncomputable def ch3Keep : List (Fin (NW P tf)) :=
  [wcR P tf m Dw Dl deg De Dt c k0 h qT, hdR P tf m Dw Dl deg De Dt c k0 h qT,
    nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0, nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2,
    nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4, nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5,
    nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6, nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7]

/-- Every kept phase-3 tape lies in phase 3's region and is none of the atom test's three counts. -/
theorem ch3Keep_pos (y : Fin (NW P tf)) (hy : y ∈ ch3Keep P tf m Dw Dl deg De Dt c k0 h qT poT) :
    2 + NL P + k0 ≤ y.val ∧ y.val < 2 + NL P + oA Dw Dl k0 ∧
      y ≠ x1R P tf m Dw Dl deg De Dt c k0 h ∧ y ≠ x2R P tf m Dw Dl deg De Dt c k0 h ∧
      y ≠ lcR P tf m Dw Dl deg De Dt c k0 h qT := by
  obtain ⟨v1, v2, vl, v0⟩ := x12R_vals P tf m Dw Dl deg De Dt c k0 h qT poT
  have t1 := FrontCh3P.tP_eq Dw
  have t2 := FrontCh3P.tP_eq Dl
  have hW1 : WT 1 9 = 15 := rfl
  have hoA := ch3_lt Dw Dl k0
  have hWT2 : WT 10 56 = 71 := rfl
  have hET : FrontEntriesStage.ET = 22 := rfl
  have key : ∀ vy : ℕ, y.val = vy → 2 + NL P + k0 ≤ vy → vy < 2 + NL P + oA Dw Dl k0 →
      vy ≠ (x1R P tf m Dw Dl deg De Dt c k0 h).val → vy ≠ (x2R P tf m Dw Dl deg De Dt c k0 h).val →
      vy ≠ (lcR P tf m Dw Dl deg De Dt c k0 h qT).val →
      2 + NL P + k0 ≤ y.val ∧ y.val < 2 + NL P + oA Dw Dl k0 ∧
        y ≠ x1R P tf m Dw Dl deg De Dt c k0 h ∧ y ≠ x2R P tf m Dw Dl deg De Dt c k0 h ∧
        y ≠ lcR P tf m Dw Dl deg De Dt c k0 h qT := fun vy e a b n1 n2 n3 =>
    ⟨by omega, by omega, fun h' => n1 (by rw [← e, h']), fun h' => n2 (by rw [← e, h']),
      fun h' => n3 (by rw [← e, h'])⟩
  simp only [ch3Keep, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ (FrontCh3P.wcT_val P tf Dw Dl (k0 + 4) _ _) (by omega) (by omega) (by rw [v1]; omega)
      (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ (FrontCh3P.hdT_val P tf Dw Dl (k0 + 4) _ _) (by omega) (by omega) (by rw [v1]; omega)
      (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ v0 (by omega) (by omega) (by rw [v1]; omega) (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ (show (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2).val =
        2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 3) from
      FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 2 (by decide) (by decide) (by decide))
      (by omega) (by omega) (by rw [v1]; omega) (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ (show (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4).val =
        2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 5) from
      FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 4 (by decide) (by decide) (by decide))
      (by omega) (by omega) (by rw [v1]; omega) (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ (show (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5).val =
        2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 6) from
      FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 5 (by decide) (by decide) (by decide))
      (by omega) (by omega) (by rw [v1]; omega) (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ (show (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val =
        2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 7) from
      FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 6 (by decide) (by decide) (by decide))
      (by omega) (by omega) (by rw [v1]; omega) (by rw [v2]; omega) (by rw [vl]; omega)
  · exact key _ (show (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7).val =
        2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 8) from
      FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 7 (by decide) (by decide) (by decide))
      (by omega) (by omega) (by rw [v1]; omega) (by rw [v2]; omega) (by rw [vl]; omega)

end PathStages

section PathStages2
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-- **The atom test on the valid path** (verdict `0`): the next branch bit `false`; the low tapes and phase 3's read
tapes kept, heads kept. -/
theorem atA_step (q En L : ℕ) (x r : List Bool) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (Kc Kd : ℕ)
    (hA : FrontAtP.AtomsOK r x.length q En x.length pos pay Kc Kd)
    (hv : FrontAtomLoop.verdictOf q (FrontAtomStageL.capP x.length) L m En pay = 0)
    (H : Fin (NW P tf) → ℕ) (A1 : Fin (NW P tf) → List Bool) (p1 : PristineH P tf H A1 (oA Dw Dl k0))
    (hH : ∀ y : Fin (NW P tf), 2 + NL P + k0 ≤ y.val → H y = 0)
    (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0) (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0)
    (hR : A1 rT = frame r ∧ H rT = 0) (hq : A1 qT = List.replicate q true ∧ H qT = 0)
    (e3 : A1 (x1R P tf m Dw Dl deg De Dt c k0 h) = List.replicate x.length true)
    (e4 : A1 (x2R P tf m Dw Dl deg De Dt c k0 h) = List.replicate x.length true)
    (e2 : A1 (lcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate L true)
    (e6 : A1 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) = List.replicate En true) :
    ∃ (H2 : Fin (NW P tf) → ℕ) (A2 : Fin (NW P tf) → List Bool),
      Step (FrontAtP.atM P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT (x1R P tf m Dw Dl deg De Dt c k0 h) qT
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) (x2R P tf m Dw Dl deg De Dt c k0 h)
        (lcR P tf m Dw Dl deg De Dt c k0 h qT) m) (FrontAtP.atCost m r x.length q En x.length L Kc Kd pay)
        H A1 H2 A2 ∧
      readTapeBit (A2 (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) (H2 (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) =
        false ∧
      PristineH P tf H2 A2 (o5 Dw Dl k0) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A2 y = A1 y ∧ H2 y = H y) ∧
      (∀ y ∈ ch3Keep P tf m Dw Dl deg De Dt c k0 h qT poT, A2 y = A1 y ∧ H2 y = H y) := by
  obtain ⟨v1, v2, vl, v0⟩ := x12R_vals P tf m Dw Dl deg De Dt c k0 h qT poT
  have t1 := FrontCh3P.tP_eq Dw
  have t2 := FrontCh3P.tP_eq Dl
  have hW1 : WT 1 9 = 15 := rfl
  have hoA := ch3_lt Dw Dl k0
  have hWT2 : WT 10 56 = 71 := rfl
  have hET : FrontEntriesStage.ET = 22 := rfl
  have hne : ∀ a b : Fin (NW P tf), a.val ≠ b.val → a ≠ b := fun a b hab e => hab (congrArg Fin.val e)
  obtain ⟨H2, A2, s2, a2, b2, L2, p2⟩ := FrontAtP.atP_step P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT
    (x1R P tf m Dw Dl deg De Dt c k0 h) qT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0)
    (x2R P tf m Dw Dl deg De Dt c k0 h) (lcR P tf m Dw Dl deg De Dt c k0 h qT) m r x.length q En x.length L pos pay
    Kc Kd hA H A1 p1
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hrL.1, by omega⟩
      · rw [v1]; constructor <;> omega
      · exact ⟨hqL.1, by omega⟩
      · rw [v0]; constructor <;> omega
      · rw [v2]; constructor <;> omega
      · rw [vl]; constructor <;> omega)
    (hne _ _ (by rw [v1, v2]; omega)) (hne _ _ (by rw [v1, vl]; omega)) (hne _ _ (by rw [v2, vl]; omega))
    hR ⟨e3, hH _ (by rw [v1]; omega)⟩ hq ⟨e6, hH _ (by rw [v0]; omega)⟩ ⟨e4, hH _ (by rw [v2]; omega)⟩
    ⟨e2, hH _ (by rw [vl]; omega)⟩
  refine ⟨H2, A2, s2, ?_, p2, fun y hy => L2 y (by omega) (hne _ _ (by rw [v1]; omega))
    (hne _ _ (by rw [v2]; omega)) (hne _ _ (by rw [vl]; omega)), fun y hy => ?_⟩
  · unfold vtR; rw [a2, b2, regTape_read]; simp [hv]
  · obtain ⟨g1, g2, n1, n2, n3⟩ := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT y hy
    exact L2 y g2 n1 n2 n3

end PathStages2

section PathStages3
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop (bank rlR rndM wSl)

theorem nuR_vals :
    (wcR P tf m Dw Dl deg De Dt c k0 h qT).val = 2 + NL P + ((k0 + 4) + (3 + 2 * Dw)) ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2).val =
      2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 3) ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4).val =
      2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 5) ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5).val =
      2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 6) ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val =
      2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 7) ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7).val =
      2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 8) :=
  ⟨FrontCh3P.wcT_val P tf Dw Dl (k0 + 4) _ _,
    FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 2 (by decide) (by decide) (by decide),
    FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 4 (by decide) (by decide) (by decide),
    FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 5 (by decide) (by decide) (by decide),
    FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 6 (by decide) (by decide) (by decide),
    FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 7 (by decide) (by decide) (by decide)⟩

set_option maxHeartbeats 1000000 in
/-- **Phase 5 on the valid path.** -/
theorem c5_step (es : List (Bool × Bool × ℕ)) (tail : List Bool) (s Wn q sys aux cb W Ce Ct Wa cw : ℕ)
    (sb rest : List Bool) (F : FrontFoldLoop.FoldIn m q)
    (hes : (sys + aux) * s ≤ es.length) (hWn : ∀ e < es.length, (natWord (FrontFmtCA.codeE es e)).length ≤ Wn)
    (hcapC : (sys + aux + 1) * (2 * (s * Wn) + 2 * Wn + 3) + s + (sys + aux) ≤ 2 * W + 2)
    (hsb : sb.length = sys * q) (hcapB1 : (sys + aux + 1) * (2 * q + 1) + q + sys + aux + 1 ≤ 2 * W + 2)
    (hcapB2 : natBitLength 3 + natBitLength sys + natBitLength aux + natBitLength cb + 1 ≤ 2 * W + 2)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ value Dt Ct W)
    (henv : ∀ X < F.nv, FrontFoldLoop.EnvFit (F.car X) deg (value De Ce W))
    (hcw : ∀ X < F.nv, FrontFoldLoop.rcost (PwM m) (CwM m) F (value De Ce W) Wa X ≤ cw)
    (hcwT : cw + 1 ≤ value Dt Ct W)
    (hlen : ∀ X ≤ F.nv, ∀ t,
      (F.st deg (value De Ce W) (value Dt Ct W) X (PwM m).t (CwM m).t t).length ≤ value Dt Ct W)
    (hys : (FrontFmtBM.rows q sb sys ++ List.replicate aux (List.replicate q false)).flatMap frame =
      F.ys.flatMap frame)
    (has : FrontFmtCA.itemsOf es s (sys + aux) = F.as.flatMap frame) (hFs : F.sys = sys) (hFn : F.nv = sys + aux)
    (H2 : Fin (NW P tf) → ℕ) (A2 : Fin (NW P tf) → List Bool) (p2 : PristineH P tf H2 A2 (o5 Dw Dl k0))
    (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0) (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) (hpq : poT ≠ qT)
    (hr : A2 rT = frame (FrontTW.entsW es ++ tail) ∧ H2 rT = 0)
    (hpo : A2 poT = FrontFmtBM.hdrOf sys aux cb ++ sb ++ rest ∧ H2 poT = 0)
    (hq : A2 qT = List.replicate q true ∧ H2 qT = 0)
    (hW : A2 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate W true ∧ H2 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = 0)
    (hs : A2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2) = List.replicate s true ∧
      H2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2) = 0)
    (hsy : A2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) = List.replicate sys true ∧
      H2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) = 0)
    (hax : A2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5) = List.replicate aux true ∧
      H2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5) = 0)
    (hnv : A2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) = List.replicate (sys + aux) true ∧
      H2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) = 0)
    (hnw : A2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7) = CompareMachine.word (sys + aux) ∧
      H2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7) = 0) :
    ∃ A3 : Fin (NW P tf) → List Bool,
      Step (ch5M P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT
        (wcR P tf m Dw Dl deg De Dt c k0 h qT) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
        (wcR P tf m Dw Dl deg De Dt c k0 h qT) Ce Ct)
        (ch5Cost m W (FrontTW.entsW es ++ tail).length s Wn (sys + aux) q sys aux cb W deg De Ce Dt Ct F.nv cw)
        H2 A2 H2 A3 ∧
      A3 (unR P tf m Dw Dl deg De Dt c k0 h qT rT) = FrontTW.entsW es ++ tail ∧
      A3 (ccR P tf m Dw Dl deg De Dt c k0 h) = CWConst.constWord m ∧
      A3 (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)) = ((List.range F.nv).map F.pw).flatMap frame ∧
      A3 (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) = ((List.range F.nv).map F.cw).flatMap frame ∧
      A3 (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)) = (List.range F.nv).map (F.eb deg) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + o5 Dw Dl k0 →
        y ≠ nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7 → A3 y = A2 y) ∧
      PristineH P tf H2 A3 (oC m Dw Dl deg De Dt k0) := by
  obtain ⟨vW, v2, v4, v5, v6, v7⟩ := nuR_vals P tf m Dw Dl deg De Dt c k0 h qT poT
  have t1 := FrontCh3P.tP_eq Dw
  have t2 := FrontCh3P.tP_eq Dl
  have hW1 : WT 1 9 = 15 := rfl
  have hoA := ch3_lt Dw Dl k0
  have hWT2 : WT 10 56 = 71 := rfl
  have hET : FrontEntriesStage.ET = 22 := rfl
  have hAP : o5 Dw Dl k0 = oA Dw Dl k0 + FrontAtP.AP := rfl
  have hne : ∀ a b : Fin (NW P tf), a.val ≠ b.val → a ≠ b := fun a b hab e => hab (congrArg Fin.val e)
  obtain ⟨A3, s3, u3, c3, f5, f6, f7, L3, p3⟩ := ch5_step P tf m deg De Dt (o5 Dw Dl k0)
    (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT (wcR P tf m Dw Dl deg De Dt c k0 h qT)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7) (wcR P tf m Dw Dl deg De Dt c k0 h qT) es tail s Wn q sys aux cb W W
    Ce Ct Wa cw sb rest F hes hWn hcapC hsb hcapB1 hcapB2 hWa hZ0 henv hcw hcwT hlen hys has hFs hFn H2 A2 p2
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hrL.1, by omega⟩
      · exact ⟨hpL.1, by omega⟩
      · exact ⟨hqL.1, by omega⟩
      · rw [vW]; constructor <;> omega
      · rw [v2]; constructor <;> omega
      · rw [v4]; constructor <;> omega
      · rw [v5]; constructor <;> omega
      · rw [v6]; constructor <;> omega
      · rw [v7]; constructor <;> omega
      · rw [vW]; constructor <;> omega)
    ⟨hne _ _ (by rw [vW]; omega), hne _ _ (by rw [v6]; omega), hne _ _ (by rw [v2]; omega),
      hne _ _ (by rw [v6, v2]; omega), hne _ _ (by rw [vW, v6]; omega), hne _ _ (by rw [vW, v2]; omega), hpq,
      hne _ _ (by rw [v4]; omega), hne _ _ (by rw [v5]; omega), hne _ _ (by rw [v4]; omega),
      hne _ _ (by rw [v5]; omega), hne _ _ (by rw [v4, v5]; omega), hne _ _ (by rw [vW]; omega),
      hne _ _ (by rw [vW]; omega), hne _ _ (by rw [vW, v4]; omega), hne _ _ (by rw [vW, v5]; omega),
      hne _ _ (by rw [v4, v7]; omega)⟩
    hr hpo hq hW hs hsy hax hnv hnw hW
  exact ⟨A3, s3, u3, c3, f5, f6, f7, L3, p3⟩

set_option maxHeartbeats 1000000 in
/-- **C1's call on the valid path.** -/
theorem cC_step {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool) (W cr nL : ℕ)
    (hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) nL (fun _ => 0)
        (bank (fun _ => List.replicate W false) (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src 0) 0) W) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ),
        An = bank D (rlR (2 * W + 2) (C1Gates.Sj Cs lits cb V po src V) k) W)
    (R : Machine.SelectionReq) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre R)
    (hreq : C1Asm.reqWord q (Ledger.rowBr cr q) (C1Gates.gtF Cs lits V) (C1Gates.npF lits V) (C1Gates.GF Cs lits V)
      (C1Gates.PF Cs lits cb V) = Plan.selWord R)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ 2 * W + 2)
    (hcap2 : q + Ledger.rowBr cr q + C1Gates.gtF Cs lits V + C1Gates.npF lits V + 6 * (natBitLength q +
      natBitLength (Ledger.rowBr cr q) + natBitLength (C1Gates.gtF Cs lits V) + natBitLength (C1Gates.npF lits V)) +
        (frame (Plan.selWord R)).length + 50 ≤ 2 * W + 2)
    (hcapC : 8 * (SelectionMachine.selArgmin R).length + 2 * (natListWord (SelectionMachine.selArgmin R)).length + 17 ≤
      2 * W + 2)
    (H2 : Fin (NW P tf) → ℕ) (A3 : Fin (NW P tf) → List Bool) (p3 : PristineH P tf H2 A3 (oC m Dw Dl deg De Dt k0))
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0)
    (hpq : poT ≠ qT)
    (hpo : A3 poT = po ∧ H2 poT = 0) (hq : A3 qT = List.replicate q true ∧ H2 qT = 0)
    (hsr : A3 (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) = src ∧
      H2 (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) = 0)
    (hW : A3 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate W true ∧
      H2 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = 0)
    (hV : A3 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) = List.replicate V true ∧
      H2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) = 0) :
    ∃ A4 : Fin (NW P tf) → List Bool,
      Step (FrontC1D.c1M P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
        (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) cr)
        (FrontC1D.c1Cost W V (nL + 1 + ((2 * C1Asm.asmCost cr q (C1Gates.gtF Cs lits V) (C1Gates.npF lits V)
          (C1Gates.GF Cs lits V) (C1Gates.PF Cs lits cb V) + 2) + 1 + ((Plan.c1sized d c.E₁ c.c₁).budget ⟨R, hpre⟩ + 1 +
            (2 * C1Stage.convCost (SelectionMachine.selArgmin R) + 2))))) H2 A3 H2 A4 ∧
      A4 (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT) = frame (natListWord (SelectionMachine.selArgmin R)) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + oC m Dw Dl deg De Dt k0 → A4 y = A3 y) ∧
      PristineH P tf H2 A4 (oE m Dw Dl deg De Dt c k0) := by
  obtain ⟨vW, v2, v4, v5, v6, v7⟩ := nuR_vals P tf m Dw Dl deg De Dt c k0 h qT poT
  have t1 := FrontCh3P.tP_eq Dw
  have t2 := FrontCh3P.tP_eq Dl
  have hW1 : WT 1 9 = 15 := rfl
  have hoA := ch3_lt Dw Dl k0
  have hWT2 : WT 10 56 = 71 := rfl
  have hET : FrontEntriesStage.ET = 22 := rfl
  have hNSF := nsf_ge m deg De Dt
  have hne : ∀ a b : Fin (NW P tf), a.val ≠ b.val → a ≠ b := fun a b hab e => hab (congrArg Fin.val e)
  have vF6 : (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val = 2 + NL P + (o5 Dw Dl k0 + 50 + 6) :=
    fiT_val P tf m deg De Dt (o5 Dw Dl k0) _ rT poT qT _ _ _ _ _ _ _ 6 (by norm_num) (by norm_num)
  have hC5 : oC m Dw Dl deg De Dt k0 = o5 Dw Dl k0 + 50 + NSF m deg De Dt := by unfold oC CH5; omega
  have hAP : o5 Dw Dl k0 = oA Dw Dl k0 + FrontAtP.AP := rfl
  obtain ⟨A4, s4, o4, L4, p4⟩ := FrontC1D.c1_step P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h)
    poT qT (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) Cs lits cb V po src W cr nL hloop R hpre hreq hcap1 hcap2 hcapC H2 A3
    p3
    (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨hpL.1, by omega⟩
      · exact ⟨hqL.1, by omega⟩
      · rw [vF6]; constructor <;> omega
      · rw [vW]; constructor <;> omega
      · rw [v6]; constructor <;> omega)
    hpq (hne _ _ (by rw [vF6]; omega)) (hne _ _ (by rw [vW]; omega)) (hne _ _ (by rw [vF6]; omega))
    (hne _ _ (by rw [vW]; omega)) (hne _ _ (by rw [vF6, vW]; omega)) hpo hq hsr hW hV
  exact ⟨A4, s4, o4, L4, p4⟩

end PathStages3

section PathPos
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))

theorem wcR_v : (wcR P tf m Dw Dl deg De Dt c k0 h qT).val = 2 + NL P + ((k0 + 4) + (3 + 2 * Dw)) :=
  FrontCh3P.wcT_val P tf Dw Dl (k0 + 4) _ _
theorem hdR_v : (hdR P tf m Dw Dl deg De Dt c k0 h qT).val =
    2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + 2) := FrontCh3P.hdT_val P tf Dw Dl (k0 + 4) _ _
theorem nuR_v0 : (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val =
    2 + NL P + (k0 + 4 + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 0) :=
  FrontCh3P.nuT0_val P tf Dw Dl (k0 + 4) _ _ _
theorem nuR_v6 : (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val =
    2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 7) :=
  FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 6 (by decide) (by decide) (by decide)
theorem nuR_v7 : (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7).val =
    2 + NL P + ((k0 + 4) + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 8) :=
  FrontCh3P.nuT_val P tf Dw Dl (k0 + 4) _ qT poT 7 (by decide) (by decide) (by decide)
theorem unR_v : (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val = 2 + NL P + (o5 Dw Dl k0 + 2) :=
  unT_val P tf m deg De Dt (o5 Dw Dl k0) _ rT _
theorem ccR_v : (ccR P tf m Dw Dl deg De Dt c k0 h).val = 2 + NL P + (o5 Dw Dl k0 + 40 + 0) :=
  ccO_val P tf m deg De Dt (o5 Dw Dl k0) _
theorem fiR_v (j : ℕ) (hj : j < 10) (h4 : 4 < j) :
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT j hj).val = 2 + NL P + (o5 Dw Dl k0 + 50 + j) :=
  fiT_val P tf m deg De Dt (o5 Dw Dl k0) _ rT poT qT _ _ _ _ _ _ _ j hj h4

/-- The offsets, as plain numbers. -/
theorem offs : FrontCh3P.tP Dw = 14 + 2 * Dw ∧ FrontCh3P.tP Dl = 14 + 2 * Dl ∧ WT 1 9 = 15 ∧
    oA Dw Dl k0 = k0 + 4 + FrontCh3P.tP Dw + FrontCh3P.tP Dl + 8 + 8 + WT 1 9 + 71 + 22 ∧
    o5 Dw Dl k0 = oA Dw Dl k0 + FrontAtP.AP ∧
    oC m Dw Dl deg De Dt k0 = o5 Dw Dl k0 + 50 + NSF m deg De Dt ∧ 1225 ≤ NSF m deg De Dt := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, nsf_ge m deg De Dt⟩
  · have := ch3_lt Dw Dl k0; have e : WT 10 56 = 71 := rfl; have e2 : FrontEntriesStage.ET = 22 := rfl; omega
  · unfold oC CH5; omega

set_option maxHeartbeats 1000000 in
/-- The positions the valid path reads its tapes at (every offset fact in one place). -/
theorem rest_pos (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) :
    let n7 := nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7
    (poT.val < 2 + NL P + o5 Dw Dl k0 ∧ poT ≠ n7) ∧ (qT.val < 2 + NL P + o5 Dw Dl k0 ∧ qT ≠ n7) ∧
    ((wcR P tf m Dw Dl deg De Dt c k0 h qT).val < 2 + NL P + o5 Dw Dl k0 ∧ wcR P tf m Dw Dl deg De Dt c k0 h qT ≠ n7) ∧
    ((hdR P tf m Dw Dl deg De Dt c k0 h qT).val < 2 + NL P + o5 Dw Dl k0 ∧ hdR P tf m Dw Dl deg De Dt c k0 h qT ≠ n7) ∧
    ((nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val < 2 + NL P + o5 Dw Dl k0 ∧
      nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0 ≠ n7) ∧
    ((nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val < 2 + NL P + o5 Dw Dl k0 ∧
      nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6 ≠ n7) ∧
    poT.val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (hdR P tf m Dw Dl deg De Dt c k0 h qT).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (ccR P tf m Dw Dl deg De Dt c k0 h).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    (wcR P tf m Dw Dl deg De Dt c k0 h qT).val < 2 + NL P + oC m Dw Dl deg De Dt k0 ∧
    2 + NL P + o5 Dw Dl k0 ≤ (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val ∧
    2 + NL P + o5 Dw Dl k0 ≤ (ccR P tf m Dw Dl deg De Dt c k0 h).val ∧
    2 + NL P + o5 Dw Dl k0 ≤ (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)).val ∧
    2 + NL P + o5 Dw Dl k0 ≤ (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val ∧
    2 + NL P + o5 Dw Dl k0 ≤ (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)).val ∧
    2 + NL P + k0 ≤ (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT).val := by
  intro n7
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := offs m Dw Dl deg De Dt k0
  have hne : ∀ a b : Fin (NW P tf), a.val ≠ b.val → a ≠ b := fun a b hab e => hab (congrArg Fin.val e)
  obtain ⟨q1, q2⟩ := hqL
  obtain ⟨p1', p2'⟩ := hpL
  exact ⟨⟨by omega, hne _ _ (fun e => by have h' := e.trans (nuR_v7 P tf m Dw Dl deg De Dt c k0 h qT poT); clear e; omega)⟩, ⟨by omega, hne _ _ (fun e => by have h' := e.trans (nuR_v7 P tf m Dw Dl deg De Dt c k0 h qT poT); clear e; omega)⟩,
    ⟨(wcR_v P tf m Dw Dl deg De Dt c k0 h qT).trans_lt (by omega), hne _ _ (fun e => by have h' := (wcR_v P tf m Dw Dl deg De Dt c k0 h qT).symm.trans (e.trans (nuR_v7 P tf m Dw Dl deg De Dt c k0 h qT poT)); clear e; omega)⟩, ⟨(hdR_v P tf m Dw Dl deg De Dt c k0 h qT).trans_lt (by omega), hne _ _ (fun e => by have h' := (hdR_v P tf m Dw Dl deg De Dt c k0 h qT).symm.trans (e.trans (nuR_v7 P tf m Dw Dl deg De Dt c k0 h qT poT)); clear e; omega)⟩,
    ⟨(nuR_v0 P tf m Dw Dl deg De Dt c k0 h qT poT).trans_lt (by omega), hne _ _ (fun e => by have h' := (nuR_v0 P tf m Dw Dl deg De Dt c k0 h qT poT).symm.trans (e.trans (nuR_v7 P tf m Dw Dl deg De Dt c k0 h qT poT)); clear e; omega)⟩, ⟨(nuR_v6 P tf m Dw Dl deg De Dt c k0 h qT poT).trans_lt (by omega), hne _ _ (fun e => by have h' := (nuR_v6 P tf m Dw Dl deg De Dt c k0 h qT poT).symm.trans (e.trans (nuR_v7 P tf m Dw Dl deg De Dt c k0 h qT poT)); clear e; omega)⟩,
    by omega, (unR_v P tf m Dw Dl deg De Dt c k0 h qT rT).trans_lt (by omega), (hdR_v P tf m Dw Dl deg De Dt c k0 h qT).trans_lt (by omega), (ccR_v P tf m Dw Dl deg De Dt c k0 h).trans_lt (by omega), (fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num) (by norm_num)).trans_lt (by omega), (fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num) (by norm_num)).trans_lt (by omega), (fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num) (by norm_num)).trans_lt (by omega), (nuR_v0 P tf m Dw Dl deg De Dt c k0 h qT poT).trans_lt (by omega), (nuR_v6 P tf m Dw Dl deg De Dt c k0 h qT poT).trans_lt (by omega), (wcR_v P tf m Dw Dl deg De Dt c k0 h qT).trans_lt (by omega),
    (Nat.add_le_add_left (Nat.le_add_right (o5 Dw Dl k0) 2) (2 + NL P)).trans_eq (unR_v P tf m Dw Dl deg De Dt c k0 h qT rT).symm, (Nat.add_le_add_left (le_trans (Nat.le_add_right (o5 Dw Dl k0) 40) (Nat.le_add_right _ 0)) (2 + NL P)).trans_eq (ccR_v P tf m Dw Dl deg De Dt c k0 h).symm, (Nat.add_le_add_left (le_trans (Nat.le_add_right (o5 Dw Dl k0) 50) (Nat.le_add_right _ 5)) (2 + NL P)).trans_eq (fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num) (by norm_num)).symm, (Nat.add_le_add_left (le_trans (Nat.le_add_right (o5 Dw Dl k0) 50) (Nat.le_add_right _ 6)) (2 + NL P)).trans_eq (fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num) (by norm_num)).symm, (Nat.add_le_add_left (le_trans (Nat.le_add_right (o5 Dw Dl k0) 50) (Nat.le_add_right _ 7)) (2 + NL P)).trans_eq (fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num) (by norm_num)).symm,
    le_trans (Nat.add_le_add_left (Nat.le_add_right k0 4) _) (ecR_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT)⟩

end PathPos

/-! ## The valid path -/

section Path
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop (bank rlR rndM wSl)

theorem c1R_ge : 2 + NL P + oC m Dw Dl deg De Dt k0 ≤ (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val := by
  unfold c1R FrontC1D.c1O
  rw [sl_none P tf _ _ _ _ (FrontCh5.insL_none_of P tf _ _ (by
    intro p hp
    simp only [FrontC1D.c1L, List.mem_cons, List.not_mem_nil, or_false] at hp
    have e : (FrontC1D.stL c (C1Stage.outT c)).val = 1436 + C1Stage.TC c + 1 := rfl
    have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega))), rg_val]
  omega

set_option maxHeartbeats 2000000 in
/-- **The valid path at mode `m` up to the front's end** (the entries pass, every atom passes): the copy of `x`,
phase 3, the atom test, phase 5 and C1's call, each step; then the table writer's sources and the count `1^W` on their
tapes, heads `0`, the end's regions pristine. -/
theorem rest_mid
    (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db : ℕ) (cdf : Bool) (Cδ Ce Ct cr : ℕ)
    (q sys aux cb : ℕ) (x r restP : List Bool) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (Kc Kd : ℕ)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) (hpq : poT ≠ qT)
    (hX : A (FrontPh1.xT P tf) = frame x ∧ H (FrontPh1.xT P tf) = 0) (hq : A qT = List.replicate q true ∧ H qT = 0)
    (hR : A rT = frame r ∧ H rT = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hx : r.length + 1 ≤ x.length)
    (hN : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (hE : (FrontEntriesRef.entScan ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) r).isSome = true)
    (hA : FrontAtP.AtomsOK r x.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length pos pay Kc Kd)
    (hv : FrontAtomLoop.verdictOf q (FrontAtomStageL.capP x.length) ((q + 1) ^ Dl) m
      ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) pay = 0)
    (es : List (Bool × Bool × ℕ)) (tail : List Bool) (Wn Wa cw : ℕ) (sb rest : List Bool) (F : FrontFoldLoop.FoldIn m q)
    (hres : r = FrontTW.entsW es ++ tail) (hrP : restP = sb ++ rest)
    (hes : (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q ≤ es.length)
    (hWn : ∀ e < es.length, (natWord (FrontFmtCA.codeE es e)).length ≤ Wn)
    (hcapC : (sys + aux + 1) * (2 * (Ledger.rowBSparse h0 h1 2 Cδ q * Wn) + 2 * Wn + 3) +
      Ledger.rowBSparse h0 h1 2 Cδ q + (sys + aux) ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hsb : sb.length = sys * q)
    (hcapB1 : (sys + aux + 1) * (2 * q + 1) + q + sys + aux + 1 ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hcapB2 : natBitLength 3 + natBitLength sys + natBitLength aux + natBitLength cb + 1 ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ value Dt Ct (Kw * (q + 1) ^ Dw))
    (henv : ∀ X < F.nv, FrontFoldLoop.EnvFit (F.car X) deg (value De Ce (Kw * (q + 1) ^ Dw)))
    (hcw : ∀ X < F.nv, FrontFoldLoop.rcost (PwM m) (CwM m) F (value De Ce (Kw * (q + 1) ^ Dw)) Wa X ≤ cw)
    (hcwT : cw + 1 ≤ value Dt Ct (Kw * (q + 1) ^ Dw))
    (hlen : ∀ X ≤ F.nv, ∀ t, (F.st deg (value De Ce (Kw * (q + 1) ^ Dw)) (value Dt Ct (Kw * (q + 1) ^ Dw)) X
      (PwM m).t (CwM m).t t).length ≤ value Dt Ct (Kw * (q + 1) ^ Dw))
    (hys : (FrontFmtBM.rows q sb sys ++ List.replicate aux (List.replicate q false)).flatMap frame =
      F.ys.flatMap frame)
    (has : FrontFmtCA.itemsOf es (Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux) = F.as.flatMap frame)
    (hFs : F.sys = sys) (hFn : F.nv = sys + aux)
    (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (nL : ℕ)
    (hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) nL (fun _ => 0)
        (bank (fun _ => List.replicate (Kw * (q + 1) ^ Dw) false)
          (rlR (2 * (Kw * (q + 1) ^ Dw) + 2) (C1Gates.Sj Cs lits cb (sys + aux)
            (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
            (((List.range F.nv).map F.cw).flatMap frame) 0) 0) (Kw * (q + 1) ^ Dw)) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ),
        An = bank D (rlR (2 * (Kw * (q + 1) ^ Dw) + 2) (C1Gates.Sj Cs lits cb (sys + aux)
          (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
          (((List.range F.nv).map F.cw).flatMap frame) (sys + aux)) k) (Kw * (q + 1) ^ Dw))
    (R : Machine.SelectionReq) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre R)
    (hreq : C1Asm.reqWord q (Ledger.rowBr cr q) (C1Gates.gtF Cs lits (sys + aux)) (C1Gates.npF lits (sys + aux))
      (C1Gates.GF Cs lits (sys + aux)) (C1Gates.PF Cs lits cb (sys + aux)) = Plan.selWord R)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hcap2 : q + Ledger.rowBr cr q + C1Gates.gtF Cs lits (sys + aux) + C1Gates.npF lits (sys + aux) +
      6 * (natBitLength q + natBitLength (Ledger.rowBr cr q) + natBitLength (C1Gates.gtF Cs lits (sys + aux)) +
        natBitLength (C1Gates.npF lits (sys + aux))) + (frame (Plan.selWord R)).length + 50 ≤
          2 * (Kw * (q + 1) ^ Dw) + 2)
    (hcapC1 : 8 * (SelectionMachine.selArgmin R).length + 2 * (natListWord (SelectionMachine.selArgmin R)).length + 17 ≤
      2 * (Kw * (q + 1) ^ Dw) + 2)
    :
    ∃ (A0 A1 : Fin (NW P tf) → List Bool) (H2 : Fin (NW P tf) → ℕ) (A2 A3 A4 : Fin (NW P tf) → List Bool),
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf (FrontPh1.xT P tf)) k0 (hr1 tf m Dw Dl deg De Dt c k0 h))
        RecoveryColdWitnessCopy.machine) (8 * x.length + 14) H A H A0 ∧
      Step (FrontCh3P.ch3M P tf Dw Kw Dl (k0 + 4) (hr2 tf m Dw Dl deg De Dt c k0 h) qT (cxR P tf m Dw Dl deg De Dt c k0 h)
        rT poT (FrontTW.modeBit m) Kb Db cdf ζ Cδ) (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r)
        H A0 H A1 ∧
      readTapeBit (A1 (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) (H (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) =
        true ∧
      Step (FrontAtP.atM P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT (x1R P tf m Dw Dl deg De Dt c k0 h) qT
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) (x2R P tf m Dw Dl deg De Dt c k0 h)
        (lcR P tf m Dw Dl deg De Dt c k0 h qT) m)
        (FrontAtP.atCost m r x.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length ((q + 1) ^ Dl) Kc Kd pay)
        H A1 H2 A2 ∧
      readTapeBit (A2 (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) (H2 (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) =
        false ∧
      Step (ch5M P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT
        (wcR P tf m Dw Dl deg De Dt c k0 h qT) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
        (wcR P tf m Dw Dl deg De Dt c k0 h qT) Ce Ct)
        (ch5Cost m (Kw * (q + 1) ^ Dw) (FrontTW.entsW es ++ tail).length (Ledger.rowBSparse h0 h1 2 Cδ q)
          Wn (sys + aux) q sys aux cb (Kw * (q + 1) ^ Dw) deg De Ce Dt Ct F.nv cw) H2 A2 H2 A3 ∧
      Step (FrontC1D.c1M P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
        (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
        (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) cr)
        (FrontC1D.c1Cost (Kw * (q + 1) ^ Dw) (sys + aux) (nL + 1 + ((2 * C1Asm.asmCost cr q
          (C1Gates.gtF Cs lits (sys + aux)) (C1Gates.npF lits (sys + aux)) (C1Gates.GF Cs lits (sys + aux))
          (C1Gates.PF Cs lits cb (sys + aux)) + 2) + 1 + ((Plan.c1sized d c.E₁ c.c₁).budget ⟨R, hpre⟩ + 1 +
            (2 * C1Stage.convCost (SelectionMachine.selArgmin R) + 2))))) H2 A3 H2 A4 ∧
      PristineH P tf H2 A4 (oE m Dw Dl deg De Dt c k0) ∧
      (∀ i : Fin 10, A4 (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i) =
        srcV (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP) (FrontTW.entsW es ++ tail)
          (frame (natWord q ++ [FrontTW.modeBit m] ++ natWord 4)) (frame (natListWord (SelectionMachine.selArgmin R)))
          (CWConst.constWord m) (((List.range F.nv).map F.pw).flatMap frame)
          (((List.range F.nv).map F.cw).flatMap frame) ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux)
          ((List.range F.nv).map (F.eb deg)) i ∧
        H2 (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i) = 0) ∧
      (A4 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate (Kw * (q + 1) ^ Dw) true ∧
        H2 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = 0)
 := by
  obtain ⟨A0, A1, s0, s1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, ec, l1, p1⟩ := rest_pre P tf m Dw Dl deg De Dt c
    k0 h qT rT poT Kw h0 h1 Kb Db cdf Cδ q sys aux cb x r restP H A hPr hqL hrL hpL hX hq hR hp hx hN
  have hH : ∀ y : Fin (NW P tf), 2 + NL P + k0 ≤ y.val → H y = 0 := fun y hy => (hPr.1 y hy).2
  have hb1 : readTapeBit (A1 (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT))
      (H (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT)) = true := by
    rw [ec, hH _ (le_trans (Nat.add_le_add_left (Nat.le_add_right k0 4) _) (ecR_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT)),
      hE]; rfl
  -- the atom test
  obtain ⟨H2, A2, s2, hb2, p2, LL2, K2⟩ := atA_step P tf m Dw Dl deg De Dt c k0 h qT rT poT q
    ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) ((q + 1) ^ Dl) x r pos pay Kc Kd hA hv H A1 p1 hH hrL hqL
    ⟨by rw [l1 rT hrL.2]; exact hR.1, hR.2⟩ ⟨by rw [l1 qT hqL.2]; exact hq.1, hq.2⟩ e3 e4 e2 e6
  have kW := K2 (wcR P tf m Dw Dl deg De Dt c k0 h qT) (by simp [ch3Keep])
  have kH := K2 (hdR P tf m Dw Dl deg De Dt c k0 h qT) (by simp [ch3Keep])
  have k0' := K2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0) (by simp [ch3Keep])
  have k2' := K2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2) (by simp [ch3Keep])
  have k4' := K2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (by simp [ch3Keep])
  have k5' := K2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5) (by simp [ch3Keep])
  have k6' := K2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (by simp [ch3Keep])
  have k7' := K2 (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7) (by simp [ch3Keep])
  have gW := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (wcR P tf m Dw Dl deg De Dt c k0 h qT) (by simp [ch3Keep])
  have gH := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (hdR P tf m Dw Dl deg De Dt c k0 h qT) (by simp [ch3Keep])
  have g0 := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0)
    (by simp [ch3Keep])
  have g2 := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
    (by simp [ch3Keep])
  have g4 := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4)
    (by simp [ch3Keep])
  have g5 := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
    (by simp [ch3Keep])
  have g6 := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6)
    (by simp [ch3Keep])
  have g7 := ch3Keep_pos P tf m Dw Dl deg De Dt c k0 h qT poT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
    (by simp [ch3Keep])
  -- phase 5
  obtain ⟨A3, s3, u3, c3, f5, f6, f7, L3, p3⟩ := c5_step P tf m Dw Dl deg De Dt c k0 h qT rT poT es tail
    (Ledger.rowBSparse h0 h1 2 Cδ q) Wn q sys aux cb (Kw * (q + 1) ^ Dw) Ce Ct Wa cw sb rest F hes hWn hcapC hsb hcapB1
    hcapB2 hWa hZ0 henv hcw hcwT hlen hys has hFs hFn H2 A2 p2 hrL hqL hpL hpq
    ⟨by rw [(LL2 rT hrL.2).1, l1 rT hrL.2, hR.1, hres], by rw [(LL2 rT hrL.2).2]; exact hR.2⟩
    ⟨by rw [(LL2 poT hpL.2).1, l1 poT hpL.2, hp.1, hrP]; simp [FrontFmtBM.hdrOf, List.append_assoc],
      by rw [(LL2 poT hpL.2).2]; exact hp.2⟩
    ⟨by rw [(LL2 qT hqL.2).1, l1 qT hqL.2]; exact hq.1, by rw [(LL2 qT hqL.2).2]; exact hq.2⟩
    ⟨by rw [kW.1]; exact e1, by rw [kW.2]; exact hH _ gW.1⟩
    ⟨by rw [k2'.1]; exact e7, by rw [k2'.2]; exact hH _ g2.1⟩
    ⟨by rw [k4'.1]; exact e8, by rw [k4'.2]; exact hH _ g4.1⟩
    ⟨by rw [k5'.1]; exact e9, by rw [k5'.2]; exact hH _ g5.1⟩
    ⟨by rw [k6'.1]; exact e10, by rw [k6'.2]; exact hH _ g6.1⟩
    ⟨by rw [k7'.1, e11]; rfl, by rw [k7'.2]; exact hH _ g7.1⟩
  -- the positions
  obtain ⟨⟨pP5, pPn⟩, ⟨pQ5, pQn⟩, ⟨pW5, pWn⟩, ⟨pH5, pHn⟩, ⟨p05, p0n⟩, ⟨p65, p6n⟩, cP, cU, cH, cK, c5', c6', c7', c0,
    c6, cW, oU, oK, o5', o6', o7', oE'⟩ := rest_pos P tf m Dw Dl deg De Dt c k0 h qT rT poT hqL hpL
  have m3P := L3 poT pP5 pPn
  have m3Q := L3 qT pQ5 pQn
  have m3W := L3 _ pW5 pWn
  have m3H := L3 _ pH5 pHn
  have m30 := L3 _ p05 p0n
  have m36 := L3 _ p65 p6n
  obtain ⟨A4, s4, o4, L4, p4⟩ := cC_step P tf m Dw Dl deg De Dt c k0 h qT rT poT Cs lits cb (sys + aux)
    (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP) (((List.range F.nv).map F.cw).flatMap frame)
    (Kw * (q + 1) ^ Dw) cr nL hloop R hpre hreq hcap1 hcap2 hcapC1 H2 A3 p3 hqL hpL hpq
    ⟨by rw [m3P, (LL2 poT hpL.2).1, l1 poT hpL.2]; exact hp.1, by rw [(LL2 poT hpL.2).2]; exact hp.2⟩
    ⟨by rw [m3Q, (LL2 qT hqL.2).1, l1 qT hqL.2]; exact hq.1, by rw [(LL2 qT hqL.2).2]; exact hq.2⟩
    ⟨f6, (p2.1 _ o6').2⟩
    ⟨by rw [m3W, kW.1]; exact e1, by rw [kW.2]; exact hH _ gW.1⟩
    ⟨by rw [m36, k6'.1]; exact e10, by rw [k6'.2]; exact hH _ g6.1⟩
  have vC := c1R_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT
  refine ⟨A0, A1, H2, A2, A3, A4, s0, s1, hb1, s2, hb2, s3, s4, p4,
    srcs_of _ _ _ _ _ _ _ _ _ _ A4 H2 _ _ _ _ _ _ _ _ _ _
      ⟨(L4 poT cP).trans (m3P.trans ((LL2 poT hpL.2).1.trans ((l1 poT hpL.2).trans hp.1))),
        (LL2 poT hpL.2).2.trans hp.2⟩
      ⟨(L4 _ cU).trans u3,
        (p2.1 _ oU).2⟩
      ⟨(L4 _ cH).trans (m3H.trans (kH.1.trans e5)),
        kH.2.trans (hH _ gH.1)⟩
      ⟨o4, (p3.1 (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT) vC).2⟩
      ⟨(L4 _ cK).trans c3,
        (p2.1 _ oK).2⟩
      ⟨(L4 _ c5').trans f5, (p2.1 _ o5').2⟩
      ⟨(L4 _ c6').trans f6, (p2.1 _ o6').2⟩
      ⟨(L4 _ c0).trans (m30.trans (k0'.1.trans e6)),
        k0'.2.trans (hH _ g0.1)⟩
      ⟨(L4 _ c6).trans (m36.trans (k6'.1.trans e10)),
        k6'.2.trans (hH _ g6.1)⟩
      ⟨(L4 _ c7').trans f7, (p2.1 _ o7').2⟩,
    (L4 _ cW).trans (m3W.trans (kW.1.trans e1)),
    kW.2.trans (hH _ gW.1)⟩

end Path

section PathRun
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop (bank rlR rndM wSl)

/-- **The valid path at mode `m`** (the entries pass, every atom passes): the chain's run through phase 5 and C1's call,
then the front's end (`hEnd`, e.g. `FrontEnd.endGood`/`endBad`) from the sources on the table writer's tapes and the
count `1^W`. -/
theorem rest_path (Pw : WM 10 56) (crT KT AT : ℕ)
    (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db : ℕ) (cdf : Bool) (Cδ Ce Ct cr : ℕ)
    (q sys aux cb : ℕ) (x r restP : List Bool) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (Kc Kd : ℕ)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) (hpq : poT ≠ qT)
    (hX : A (FrontPh1.xT P tf) = frame x ∧ H (FrontPh1.xT P tf) = 0) (hq : A qT = List.replicate q true ∧ H qT = 0)
    (hR : A rT = frame r ∧ H rT = 0)
    (hp : A poT = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP ∧ H poT = 0)
    (hx : r.length + 1 ≤ x.length)
    (hN : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (hE : (FrontEntriesRef.entScan ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) r).isSome = true)
    (hA : FrontAtP.AtomsOK r x.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length pos pay Kc Kd)
    (hv : FrontAtomLoop.verdictOf q (FrontAtomStageL.capP x.length) ((q + 1) ^ Dl) m
      ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) pay = 0)
    (es : List (Bool × Bool × ℕ)) (tail : List Bool) (Wn Wa cw : ℕ) (sb rest : List Bool) (F : FrontFoldLoop.FoldIn m q)
    (hres : r = FrontTW.entsW es ++ tail) (hrP : restP = sb ++ rest)
    (hes : (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q ≤ es.length)
    (hWn : ∀ e < es.length, (natWord (FrontFmtCA.codeE es e)).length ≤ Wn)
    (hcapC : (sys + aux + 1) * (2 * (Ledger.rowBSparse h0 h1 2 Cδ q * Wn) + 2 * Wn + 3) +
      Ledger.rowBSparse h0 h1 2 Cδ q + (sys + aux) ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hsb : sb.length = sys * q)
    (hcapB1 : (sys + aux + 1) * (2 * q + 1) + q + sys + aux + 1 ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hcapB2 : natBitLength 3 + natBitLength sys + natBitLength aux + natBitLength cb + 1 ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ value Dt Ct (Kw * (q + 1) ^ Dw))
    (henv : ∀ X < F.nv, FrontFoldLoop.EnvFit (F.car X) deg (value De Ce (Kw * (q + 1) ^ Dw)))
    (hcw : ∀ X < F.nv, FrontFoldLoop.rcost (PwM m) (CwM m) F (value De Ce (Kw * (q + 1) ^ Dw)) Wa X ≤ cw)
    (hcwT : cw + 1 ≤ value Dt Ct (Kw * (q + 1) ^ Dw))
    (hlen : ∀ X ≤ F.nv, ∀ t, (F.st deg (value De Ce (Kw * (q + 1) ^ Dw)) (value Dt Ct (Kw * (q + 1) ^ Dw)) X
      (PwM m).t (CwM m).t t).length ≤ value Dt Ct (Kw * (q + 1) ^ Dw))
    (hys : (FrontFmtBM.rows q sb sys ++ List.replicate aux (List.replicate q false)).flatMap frame =
      F.ys.flatMap frame)
    (has : FrontFmtCA.itemsOf es (Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux) = F.as.flatMap frame)
    (hFs : F.sys = sys) (hFn : F.nv = sys + aux)
    (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (nL : ℕ)
    (hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) nL (fun _ => 0)
        (bank (fun _ => List.replicate (Kw * (q + 1) ^ Dw) false)
          (rlR (2 * (Kw * (q + 1) ^ Dw) + 2) (C1Gates.Sj Cs lits cb (sys + aux)
            (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
            (((List.range F.nv).map F.cw).flatMap frame) 0) 0) (Kw * (q + 1) ^ Dw)) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ),
        An = bank D (rlR (2 * (Kw * (q + 1) ^ Dw) + 2) (C1Gates.Sj Cs lits cb (sys + aux)
          (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
          (((List.range F.nv).map F.cw).flatMap frame) (sys + aux)) k) (Kw * (q + 1) ^ Dw))
    (R : Machine.SelectionReq) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre R)
    (hreq : C1Asm.reqWord q (Ledger.rowBr cr q) (C1Gates.gtF Cs lits (sys + aux)) (C1Gates.npF lits (sys + aux))
      (C1Gates.GF Cs lits (sys + aux)) (C1Gates.PF Cs lits cb (sys + aux)) = Plan.selWord R)
    (hcap1 : 20 * (q + 2) + 4 * cr + 100 ≤ 2 * (Kw * (q + 1) ^ Dw) + 2)
    (hcap2 : q + Ledger.rowBr cr q + C1Gates.gtF Cs lits (sys + aux) + C1Gates.npF lits (sys + aux) +
      6 * (natBitLength q + natBitLength (Ledger.rowBr cr q) + natBitLength (C1Gates.gtF Cs lits (sys + aux)) +
        natBitLength (C1Gates.npF lits (sys + aux))) + (frame (Plan.selWord R)).length + 50 ≤
          2 * (Kw * (q + 1) ^ Dw) + 2)
    (hcapC1 : 8 * (SelectionMachine.selArgmin R).length + 2 * (natListWord (SelectionMachine.selArgmin R)).length + 17 ≤
      2 * (Kw * (q + 1) ^ Dw) + 2)
    (Q : (Fin (NW P tf) → ℕ) → (Fin (NW P tf) → List Bool) → Prop) (nE : ℕ)
    (hEnd : ∀ (H5 : Fin (NW P tf) → ℕ) (A5 : Fin (NW P tf) → List Bool),
      PristineH P tf H5 A5 (oE m Dw Dl deg De Dt c k0) →
      (∀ i : Fin 10, A5 (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i) =
        srcV (natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP) (FrontTW.entsW es ++ tail)
          (frame (natWord q ++ [FrontTW.modeBit m] ++ natWord 4)) (frame (natListWord (SelectionMachine.selArgmin R)))
          (CWConst.constWord m) (((List.range F.nv).map F.pw).flatMap frame)
          (((List.range F.nv).map F.cw).flatMap frame) ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux)
          ((List.range F.nv).map (F.eb deg)) i ∧
        H5 (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i) = 0) →
      (A5 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = List.replicate (Kw * (q + 1) ^ Dw) true ∧
        H5 (wcR P tf m Dw Dl deg De Dt c k0 h qT) = 0) →
      ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
        Step (FrontEnd.endM P tf Pw crT KT AT (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (oE m Dw Dl deg De Dt c k0) (hr6 tf m Dw Dl deg De Dt c k0 h)
            (oT m Dw Dl deg De Dt c k0) (hr7 tf m Dw Dl deg De Dt c k0 h)) nE H5 A5 H' A' ∧ Q H' A') :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (restM P tf m Dw Dl deg De Dt c k0 h qT rT poT Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        ((8 * x.length + 14) + 1 + (FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r + 1 +
          ((FrontAtP.atCost m r x.length q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) x.length ((q + 1) ^ Dl) Kc Kd
            pay + 1 + ((ch5Cost m (Kw * (q + 1) ^ Dw) (FrontTW.entsW es ++ tail).length (Ledger.rowBSparse h0 h1 2 Cδ q)
              Wn (sys + aux) q sys aux cb (Kw * (q + 1) ^ Dw) deg De Ce Dt Ct F.nv cw + 1 +
              (FrontC1D.c1Cost (Kw * (q + 1) ^ Dw) (sys + aux) (nL + 1 + ((2 * C1Asm.asmCost cr q
                (C1Gates.gtF Cs lits (sys + aux)) (C1Gates.npF lits (sys + aux)) (C1Gates.GF Cs lits (sys + aux))
                (C1Gates.PF Cs lits cb (sys + aux)) + 2) + 1 + ((Plan.c1sized d c.E₁ c.c₁).budget ⟨R, hpre⟩ + 1 +
                  (2 * C1Stage.convCost (SelectionMachine.selArgmin R) + 2)))) + 1 + nE)) + 1)) + 1)))
        H A H' A' ∧ Q H' A' := by
  obtain ⟨A0, A1, H2, A2, A3, A4, s0, s1, hb1, s2, hb2, s3, s4, p4, hsrc, hcnt⟩ := rest_mid P tf m Dw Dl deg De Dt c
    k0 h qT rT poT Kw h0 h1 Kb Db cdf Cδ Ce Ct cr q sys aux cb x r restP pos pay Kc Kd H A hPr hqL hrL hpL hpq hX hq hR hp
    hx hN hE hA hv es tail Wn Wa cw sb rest F hres hrP hes hWn hcapC hsb hcapB1 hcapB2 hWa hZ0 henv hcw hcwT hlen hys has
    hFs hFn Cs lits nL hloop R hpre hreq hcap1 hcap2 hcapC1
  obtain ⟨H5, A5, s5, q5⟩ := hEnd H2 A4 p4 hsrc hcnt
  have sE := Step.seq s3 (Step.seq s4 s5)
  have sV := iteF (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT) (FrontGate.rejM P tf) (Composition.machine (ch5M P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) Ce Ct)
    (Composition.machine (FrontC1D.c1M P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
            (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) cr) (FrontEnd.endM P tf Pw crT KT AT (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (oE m Dw Dl deg De Dt c k0) (hr6 tf m Dw Dl deg De Dt c k0 h)
            (oT m Dw Dl deg De Dt c k0) (hr7 tf m Dw Dl deg De Dt c k0 h)))) hb2 sE
  have sA := Step.seq s2 sV
  have sEc := iteT (ecR P tf m Dw Dl deg De Dt c k0 h qT rT poT) (Composition.machine (FrontAtP.atM P tf (oA Dw Dl k0) (hr3 tf m Dw Dl deg De Dt c k0 h) rT
        (x1R P tf m Dw Dl deg De Dt c k0 h) qT (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0)
        (x2R P tf m Dw Dl deg De Dt c k0 h) (lcR P tf m Dw Dl deg De Dt c k0 h qT) m) (iteMachine (vtR P tf m Dw Dl deg De Dt c k0 h qT rT poT) (FrontGate.rejM P tf)
    (Composition.machine (ch5M P tf m deg De Dt (o5 Dw Dl k0) (hr4 tf m Dw Dl deg De Dt c k0 h) rT poT qT
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 2)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 4) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 5)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 7)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) Ce Ct) (Composition.machine (FrontC1D.c1M P tf c (oC m Dw Dl deg De Dt k0) (hr5 tf m Dw Dl deg De Dt c k0 h) poT qT
            (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)) (wcR P tf m Dw Dl deg De Dt c k0 h qT)
            (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6) cr) (FrontEnd.endM P tf Pw crT KT AT (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT)
            (wcR P tf m Dw Dl deg De Dt c k0 h qT) (oE m Dw Dl deg De Dt c k0) (hr6 tf m Dw Dl deg De Dt c k0 h)
            (oT m Dw Dl deg De Dt c k0) (hr7 tf m Dw Dl deg De Dt c k0 h)))))) (FrontGate.rejM P tf) hb1 sA
  refine ⟨H5, A5, ?_, q5⟩
  unfold restM
  exact Step.seq s0 (Step.seq s1 sEc)

end PathRun

end NearCubicWires.WireExponent3_5.UnionMachine.FrontRest
