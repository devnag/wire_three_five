import Proof.Wire_3_5.UnionMachine.FrontCh3P
import Proof.Wire_3_5.UnionMachine.FrontFmtCA
import Proof.Wire_3_5.UnionMachine.FrontFmtW
import Proof.Wire_3_5.UnionMachine.FrontFoldStage
import Proof.Wire_3_5.UnionMachine.CWWritersJ
import Proof.MachineModel.ClockUnarySum

/-! # C6 front, the chain, phase 5: the table writer's sources (P3:3672-3674, 3092-3094, 3409-3410)

On the valid path after the atom test, seven stages on consecutive regions write what the table writer reads besides
the numbers: the guess's entries raw (`unmarkW`), each variable's atoms' codes (`caW`), the supports' bitmaps (`bmW`),
the constant atom's code (base's fixed-word printer), two unary copies (`1^q`, `1^{n0}`) and the writers' fold (every
variable's parity code, carrier code and envelope bit). Generic docks: **`stepK`** (any stage from a zero-head `Step`,
shared inputs it may consume), **`insL`** (shared slots from a list). **`ch5_step`**.

Paper quantity of the main type: the per-variable codes and envelope bits and the guess's entries (P3:3672-3674). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCh5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.BlockPlatform.UnaryCalc (tapes)

/-! ## Raising a word program's capacity -/

theorem liftW_id {ns nr : ℕ} (Pm : WM ns nr) : Pm.liftW id id = Pm := by
  induction Pm <;> simp_all [WM.liftW]

/-- A run at capacity `cap` is a run at every larger capacity. -/
theorem capUp {ns nr : ℕ} {cap cap' : ℕ} (hc : cap ≤ cap') {Pm : WM ns nr} {σ τ : WState ns nr} {n : ℕ}
    (hw : WExec cap Pm σ τ n) : WExec cap' Pm σ τ n := by
  obtain ⟨ω', e, hl, -⟩ := WExec.liftW cap cap' hc id Function.injective_id id Function.injective_id hw σ
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  rw [liftW_id] at e
  have hω : ω' = τ := WState.eq (funext hl.sh) (funext hl.st) (funext hl.val) hl.cell
  subst hω; exact e

section Dock
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- Shared slots from a list of (local tape, bank tape) pairs. -/
def insL {t : ℕ} (l : List (ℕ × Fin (NW P tf))) (i : Fin t) : Option (Fin (NW P tf)) :=
  (l.find? (fun p => p.1 == i.val)).map Prod.snd

theorem insL_some {t : ℕ} (l : List (ℕ × Fin (NW P tf))) (i : Fin t) (b : Fin (NW P tf))
    (h : insL P tf l i = some b) : (i.val, b) ∈ l := by
  unfold insL at h
  cases hf : l.find? (fun p => p.1 == i.val) with
  | none => rw [hf] at h; simp at h
  | some p =>
    rw [hf] at h
    have hm := List.mem_of_find?_eq_some hf
    have hq := List.find?_some hf
    have e : p.2 = b := by simpa using h
    have e1 : p.1 = i.val := by simpa using hq
    have hp : p = (i.val, b) := Prod.ext e1 e
    rw [← hp]; exact hm

theorem insL_none {t : ℕ} (l : List (ℕ × Fin (NW P tf))) (i : Fin t) (h : insL P tf l i = none) :
    ∀ p ∈ l, p.1 ≠ i.val := by
  unfold insL at h
  have h' : l.find? (fun p => p.1 == i.val) = none := by simpa using h
  intro p hp e
  have := List.find?_eq_none.mp h' p hp
  simp [e] at this

theorem insL_inj {t : ℕ} (l : List (ℕ × Fin (NW P tf)))
    (hd : ∀ p ∈ l, ∀ p' ∈ l, p.2 = p'.2 → p.1 = p'.1) :
    ∀ i j a, insL (t := t) P tf l i = some a → insL P tf l j = some a → i = j := by
  intro i j a hi hj
  exact Fin.ext (hd _ (insL_some P tf l i a hi) _ (insL_some P tf l j a hj) rfl)

theorem insL_low {t : ℕ} (l : List (ℕ × Fin (NW P tf))) (k0 : ℕ)
    (hl : ∀ p ∈ l, 2 + NL P ≤ p.2.val ∧ p.2.val < 2 + NL P + k0) :
    ∀ i a, insL (t := t) P tf l i = some a → 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0 :=
  fun i a hi => hl _ (insL_some P tf l i a hi)

/-- **Any stage from a zero-head run, docked** with shared inputs it may consume: its outputs at its slots, the tapes
below its region kept unless consumed, the tapes past it blank, heads unchanged. -/
theorem stepK {t s : ℕ} (p : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool)
    (hs : Step p n (fun _ => 0) tin (fun _ => 0) tout)
    (ins : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (hk : k0 + t ≤ tf)
    (hinsI : ∀ i j a, ins i = some a → ins j = some a → i = j)
    (hinsL : ∀ i a, ins i = some a → 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k0)
    (hin : ∀ i a, ins i = some a → A a = tin i ∧ H a = 0) (hnone : ∀ i, ins i = none → tin i = []) :
    Step (RecoveryFocus.machine (sl P tf ins k0 hk) p) n H A H (install (sl P tf ins k0 hk) A tout) ∧
      (∀ j, (install (sl P tf ins k0 hk) A tout) (sl P tf ins k0 hk j) = tout j) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → (∀ j, ins j = some y → tout j = tin j) →
        install (sl P tf ins k0 hk) A tout y = A y) ∧
      PristineH P tf H (install (sl P tf ins k0 hk) A tout) (k0 + t) := by
  obtain ⟨st, hinj, hpr⟩ := dockS_step P tf p n tin tout (fun _ => 0) hs ins k0 hk hinsI hinsL H A hPr hin hnone
  have hH0 : ∀ j, H (sl P tf ins k0 hk j) = 0 := by
    intro j
    cases hj : ins j with
    | some a => rw [sl_some P tf _ k0 hk j a hj]; exact (hin j a hj).2
    | none => rw [sl_none P tf _ k0 hk j hj]; exact (hPr.1 _ (by rw [rg_val]; omega)).2
  rw [ExtDecompositionBatch.dockH_existing _ H _ hH0] at st hpr
  refine ⟨st, fun j => install_slot _ hinj _ _ j, fun y hy hkp => ?_, hpr⟩
  by_cases hsh : ∃ j a, ins j = some a ∧ a = y
  · obtain ⟨j, a, hj, rfl⟩ := hsh
    calc install (sl P tf ins k0 hk) A tout a = install (sl P tf ins k0 hk) A tout (sl P tf ins k0 hk j) := by
          rw [sl_some P tf _ k0 hk j a hj]
      _ = tout j := install_slot _ hinj _ _ _
      _ = tin j := hkp j hj
      _ = A a := (hin j a hj).1.symm
  · push Not at hsh
    exact install_low P tf _ k0 hk A tout y hy (fun i b hi e => hsh i b hi e)

end Dock

/-! ## The phase's layout -/

section Layout
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- The fold's writers at mode `m`. -/
noncomputable abbrev PwM (m : Mode) := CWWritersJ.writersJ.parity m
noncomputable abbrev CwM (m : Mode) := CWWritersJ.writersJ.carrier m

/-- The fold's tape count. -/
noncomputable abbrev NSF (m : Mode) (deg De Dt : ℕ) : ℕ :=
  FrontFoldStage.NS (1220 + (PwM m).t + (CwM m).t) (tapes deg) (tapes De + tapes Dt)

/-- The phase's size. -/
noncomputable abbrev CH5 (m : Mode) (deg De Dt : ℕ) : ℕ := 50 + NSF m deg De Dt

theorem nsf_ge (m : Mode) (deg De Dt : ℕ) : 1225 ≤ NSF m deg De Dt := by
  unfold NSF FrontFoldStage.NS; omega

/-- The atoms' codes' shared inputs: the framed rest, `1^nv`, `1^s`. -/
noncomputable def caL (rT nvT sT : Fin (NW P tf)) : List (ℕ × Fin (NW P tf)) := [(0, rT), (1, nvT), (2, sT)]
/-- The bitmaps' shared inputs: the PCPP output, `1^q`, `1^sys`, `1^aux`. -/
noncomputable def bmL (poT qT syT axT : Fin (NW P tf)) : List (ℕ × Fin (NW P tf)) :=
  [(0, poT), (1, qT), (2, syT), (3, axT)]
/-- The fold's shared inputs: the bitmaps, the atoms' codes, `1^sys`, the count word, `1^q`, `1^{n0}`. -/
noncomputable def foL (m : Mode) (b c y w u v : Fin (NW P tf)) : List (ℕ × Fin (NW P tf)) :=
  [(0, b), (2, c), (4, y), (1220 + (PwM m).t + (CwM m).t + 2, w), (1220 + (PwM m).t + (CwM m).t + 3, u),
    (1220 + (PwM m).t + (CwM m).t + 4, v)]

variable (m : Mode) (deg De Dt : ℕ) (k0 : ℕ) (h : k0 + CH5 m deg De Dt ≤ tf)

include h in
theorem hc1 : k0 + WT 1 0 ≤ tf := by have := nsf_ge m deg De Dt; unfold CH5 at h; have e : WT 1 0 = 6 := rfl; omega
include h in
theorem hc2 : (k0 + 6) + WT 3 7 ≤ tf := by
  have := nsf_ge m deg De Dt; unfold CH5 at h; have e : WT 3 7 = 15 := rfl; omega
include h in
theorem hc3 : (k0 + 21) + WT 4 10 ≤ tf := by
  have := nsf_ge m deg De Dt; unfold CH5 at h; have e : WT 4 10 = 19 := rfl; omega
include h in
theorem hc4 : (k0 + 40) + 2 ≤ tf := by have := nsf_ge m deg De Dt; unfold CH5 at h; omega
include h in
theorem hc5 : (k0 + 42) + 4 ≤ tf := by have := nsf_ge m deg De Dt; unfold CH5 at h; omega
include h in
theorem hc6 : (k0 + 46) + 4 ≤ tf := by have := nsf_ge m deg De Dt; unfold CH5 at h; omega
include h in
theorem hc7 : (k0 + 50) + NSF m deg De Dt ≤ tf := by unfold CH5 at h; omega

variable (rT poT qT cT sT syT axT nvT nwT n0T : Fin (NW P tf))

/-- The raw rest. -/
noncomputable def unT : Fin (NW P tf) := stT P tf (sh1 P tf rT) cT k0 (hc1 tf m deg De Dt k0 h) 1
/-- The atoms' codes. -/
noncomputable def caO : Fin (NW P tf) :=
  stT P tf (insL P tf (caL P tf rT nvT sT)) cT (k0 + 6) (hc2 tf m deg De Dt k0 h) 3
/-- The bitmaps. -/
noncomputable def bmO : Fin (NW P tf) :=
  stT P tf (insL P tf (bmL P tf poT qT syT axT)) cT (k0 + 21) (hc3 tf m deg De Dt k0 h) 4
/-- The constant's code. -/
noncomputable def ccO : Fin (NW P tf) := sl P tf (fun _ => none) (k0 + 40) (hc4 tf m deg De Dt k0 h) (0 : Fin 2)
/-- The copies of `1^q` and `1^{n0}`. -/
noncomputable def qcT : Fin (NW P tf) := sl P tf (sh1 P tf qT) (k0 + 42) (hc5 tf m deg De Dt k0 h) (2 : Fin 4)
noncomputable def ncT : Fin (NW P tf) := sl P tf (sh1 P tf n0T) (k0 + 46) (hc6 tf m deg De Dt k0 h) (2 : Fin 4)

/-- The fold's shared slots. -/
noncomputable def foIns : Fin (NSF m deg De Dt) → Option (Fin (NW P tf)) :=
  insL P tf (foL P tf m (bmO P tf m deg De Dt k0 h poT qT cT syT axT) (caO P tf m deg De Dt k0 h rT cT sT nvT) syT nwT
    (qcT P tf m deg De Dt k0 h qT) (ncT P tf m deg De Dt k0 h n0T))

/-- The fold's kept tape `j < 10`. -/
noncomputable def fiT (j : ℕ) (hj : j < 10) : Fin (NW P tf) :=
  sl P tf (foIns P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T) (k0 + 50) (hc7 tf m deg De Dt k0 h)
    ⟨j, by have := nsf_ge m deg De Dt; omega⟩

/-- **Phase 5's machine.** -/
noncomputable def ch5M (Ce Ct : ℕ) :=
  Composition.machine (wfD P tf FrontFmtW.unmarkW (sh1 P tf rT) cT k0 (hc1 tf m deg De Dt k0 h))
  (Composition.machine (wfD P tf FrontFmtCA.caW (insL P tf (caL P tf rT nvT sT)) cT (k0 + 6) (hc2 tf m deg De Dt k0 h))
  (Composition.machine (wfD P tf FrontFmtBM.bmW (insL P tf (bmL P tf poT qT syT axT)) cT (k0 + 21)
    (hc3 tf m deg De Dt k0 h))
  (Composition.machine (RecoveryFocus.machine (sl P tf (fun _ => none) (k0 + 40) (hc4 tf m deg De Dt k0 h))
    (HierarchyFixedWord.machine (CWConst.constWord m)))
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf qT) (k0 + 42) (hc5 tf m deg De Dt k0 h))
    ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf n0T) (k0 + 46) (hc6 tf m deg De Dt k0 h))
    ClockUnarySum.machine)
    (RecoveryFocus.machine (sl P tf (foIns P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T) (k0 + 50)
      (hc7 tf m deg De Dt k0 h)) (FrontFoldStage.stageM (PwM m) (CwM m) deg De Ce Dt Ct)))))))

end Layout

/-! ## The stages -/

section Stages
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (deg De Dt : ℕ) (k0 : ℕ) (h : k0 + CH5 m deg De Dt ≤ tf)
  (rT poT qT cT sT syT axT nvT nwT n0T : Fin (NW P tf))

/-- **The raw rest** (`FrontFmtW.unmarkW` docked): `frame r` ↦ `r`. -/
theorem unStageF (r : List Bool) (W : ℕ) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0) (hcL : 2 + NL P ≤ cT.val ∧ cT.val < 2 + NL P + k0)
    (hrc : rT ≠ cT) (hr : A rT = frame r ∧ H rT = 0) (hW : A cT = List.replicate W true ∧ H cT = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (wfD P tf FrontFmtW.unmarkW (sh1 P tf rT) cT k0 (hc1 tf m deg De Dt k0 h))
        ((11 * W + 20) + 1 + (1 + 1 + (2 * (10 * r.length + 1) + 2))) H A H A' ∧
      A' (unT P tf m deg De Dt k0 h rT cT) = r ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y) ∧
      PristineH P tf H A' (k0 + WT 1 0) := by
  obtain ⟨τ, hw, e1, e0, -⟩ := FrontFmtW.unLoop_spec [] r [] (FrontFmtW.σU (frame r))
    (by simp [FrontFmtW.σU]) rfl rfl
  obtain ⟨A1, st, o, l, p⟩ := wfN P tf FrontFmtW.unmarkW W _ _ τ (capUp (Nat.zero_le _) hw)
    (fun _ => rfl) (fun r => r.elim0) rfl (sh1 P tf rT) cT k0 (hc1 tf m deg De Dt k0 h)
    (sh1_I P tf rT) (sh1_L P tf rT k0 hrL) hcL
    (fun i e => by unfold sh1 at e; split_ifs at e; exact hrc (Option.some.inj e))
    (fun i a hi => by
      unfold sh1 at hi; split_ifs at hi with h0
      have e : i = 0 := Fin.ext h0
      subst e; exact e0)
    H A hPr
    (fun i a hi => by
      unfold sh1 at hi; split_ifs at hi with h0
      have e : i = 0 := Fin.ext h0
      subst e; rw [← Option.some.inj hi]; exact hr)
    (fun i hi => by
      unfold sh1 at hi; split_ifs at hi with h0
      have e : i = 1 := Fin.ext (by have := i.isLt; show i.val = 1; omega)
      subst e; rfl)
    hW
  refine ⟨A1, st, ?_, l, p⟩
  unfold unT; rw [o 1, e1]; rfl

/-- **The atoms' codes** (`FrontFmtCA.caW` docked): per variable, its `s` entries' code fields. -/
theorem caStageF (es : List (Bool × Bool × ℕ)) (tail : List Bool) (s Wn nv W : ℕ)
    (hes : nv * s ≤ es.length) (hWn : ∀ e < es.length, (natWord (FrontFmtCA.codeE es e)).length ≤ Wn)
    (hcap : (nv + 1) * (2 * (s * Wn) + 2 * Wn + 3) + s + nv ≤ 2 * W + 2)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A (k0 + 6))
    (hl : ∀ p ∈ caL P tf rT nvT sT, 2 + NL P ≤ p.2.val ∧ p.2.val < 2 + NL P + (k0 + 6))
    (hd : ∀ p ∈ caL P tf rT nvT sT, ∀ p' ∈ caL P tf rT nvT sT, p.2 = p'.2 → p.1 = p'.1)
    (hcL : 2 + NL P ≤ cT.val ∧ cT.val < 2 + NL P + (k0 + 6)) (hcs : cT ≠ rT ∧ cT ≠ nvT ∧ cT ≠ sT)
    (hr : A rT = frame (FrontTW.entsW es ++ tail) ∧ H rT = 0) (hnv : A nvT = List.replicate nv true ∧ H nvT = 0)
    (hs : A sT = List.replicate s true ∧ H sT = 0) (hW : A cT = List.replicate W true ∧ H cT = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (wfD P tf FrontFmtCA.caW (insL P tf (caL P tf rT nvT sT)) cT (k0 + 6) (hc2 tf m deg De Dt k0 h))
        ((11 * W + 20) + 1 + (1 + 1 + (2 * FrontFmtCA.caCost s Wn nv + 2))) H A H A' ∧
      A' (caO P tf m deg De Dt k0 h rT cT sT nvT) = FrontFmtCA.itemsOf es s nv ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + 6) → A' y = A y) ∧
      PristineH P tf H A' (k0 + 6 + WT 3 7) := by
  set σ := FrontFmtCA.σC (frame (FrontTW.entsW es ++ tail)) (List.replicate nv true) (List.replicate s true) with hσ
  obtain ⟨τ, hw, e3, e0, e1, e2, -⟩ := FrontFmtCA.caW_spec (2 * W + 2) es tail [] s Wn nv hes hWn hcap σ
    (by simp [hσ, FrontFmtCA.σC]) rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
  obtain ⟨A1, st, o, l, p⟩ := wfN P tf FrontFmtCA.caW W _ σ τ hw (fun _ => rfl) (fun _ => rfl) rfl
    (insL P tf (caL P tf rT nvT sT)) cT (k0 + 6) (hc2 tf m deg De Dt k0 h) (insL_inj P tf _ hd)
    (insL_low P tf _ _ hl) hcL
    (fun i e => by
      have hm := insL_some P tf _ i cT e
      simp only [caL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨-, e'⟩ | ⟨-, e'⟩ | ⟨-, e'⟩
      · exact hcs.1 e'
      · exact hcs.2.1 e'
      · exact hcs.2.2 e')
    (fun i a hi => by
      have hm := insL_some P tf _ i a hi
      simp only [caL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · rw [show i = 0 from Fin.ext e]; exact e0
      · rw [show i = 1 from Fin.ext e]; exact e1
      · rw [show i = 2 from Fin.ext e]; exact e2)
    H A hPr
    (fun i a hi => by
      have hm := insL_some P tf _ i a hi
      simp only [caL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
      · rw [show i = 0 from Fin.ext e]; exact hr
      · rw [show i = 1 from Fin.ext e]; exact hnv
      · rw [show i = 2 from Fin.ext e]; exact hs)
    (fun i hi => by
      have hn := insL_none P tf _ i hi
      have h0 := hn (0, rT) (by simp [caL])
      have h1 := hn (1, nvT) (by simp [caL])
      have h2 := hn (2, sT) (by simp [caL])
      have e : i = 3 := Fin.ext (by have := i.isLt; simp only at h0 h1 h2; show i.val = 3; omega)
      subst e; rfl)
    hW
  refine ⟨A1, st, ?_, l, p⟩
  unfold caO; rw [o 3]; exact e3

/-- **The bitmaps** (`FrontFmtBM.bmW` docked): the systematic supports' rows, then `aux` zero rows, framed. -/
theorem bmStageF (q sys aux cb W : ℕ) (sb rest : List Bool) (hsb : sb.length = sys * q)
    (hc1' : (sys + aux + 1) * (2 * q + 1) + q + sys + aux + 1 ≤ 2 * W + 2)
    (hc2' : natBitLength 3 + natBitLength sys + natBitLength aux + natBitLength cb + 1 ≤ 2 * W + 2)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A (k0 + 21))
    (hl : ∀ p ∈ bmL P tf poT qT syT axT, 2 + NL P ≤ p.2.val ∧ p.2.val < 2 + NL P + (k0 + 21))
    (hd : ∀ p ∈ bmL P tf poT qT syT axT, ∀ p' ∈ bmL P tf poT qT syT axT, p.2 = p'.2 → p.1 = p'.1)
    (hcL : 2 + NL P ≤ cT.val ∧ cT.val < 2 + NL P + (k0 + 21))
    (hcs : cT ≠ poT ∧ cT ≠ qT ∧ cT ≠ syT ∧ cT ≠ axT)
    (hpo : A poT = FrontFmtBM.hdrOf sys aux cb ++ sb ++ rest ∧ H poT = 0)
    (hq : A qT = List.replicate q true ∧ H qT = 0) (hsy : A syT = List.replicate sys true ∧ H syT = 0)
    (hax : A axT = List.replicate aux true ∧ H axT = 0) (hW : A cT = List.replicate W true ∧ H cT = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (wfD P tf FrontFmtBM.bmW (insL P tf (bmL P tf poT qT syT axT)) cT (k0 + 21) (hc3 tf m deg De Dt k0 h))
        ((11 * W + 20) + 1 + (1 + 1 + (2 * FrontFmtBM.bmCost q sys aux cb + 2))) H A H A' ∧
      A' (bmO P tf m deg De Dt k0 h poT qT cT syT axT) =
        (FrontFmtBM.rows q sb sys ++ List.replicate aux (List.replicate q false)).flatMap frame ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + 21) → A' y = A y) ∧
      PristineH P tf H A' (k0 + 21 + WT 4 10) := by
  set σ := FrontFmtBM.σB (FrontFmtBM.hdrOf sys aux cb ++ sb ++ rest) (List.replicate q true)
    (List.replicate sys true) (List.replicate aux true) with hσ
  obtain ⟨τ, hw, e4, e0, e1, e2, e3, -⟩ := FrontFmtBM.bmW_spec (2 * W + 2) q sys aux cb sb rest hsb hc1' hc2' σ
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
  obtain ⟨A1, st, o, l, p⟩ := wfN P tf FrontFmtBM.bmW W _ σ τ hw (fun _ => rfl) (fun _ => rfl) rfl
    (insL P tf (bmL P tf poT qT syT axT)) cT (k0 + 21) (hc3 tf m deg De Dt k0 h) (insL_inj P tf _ hd)
    (insL_low P tf _ _ hl) hcL
    (fun i e => by
      have hm := insL_some P tf _ i cT e
      simp only [bmL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨-, e'⟩ | ⟨-, e'⟩ | ⟨-, e'⟩ | ⟨-, e'⟩
      · exact hcs.1 e'
      · exact hcs.2.1 e'
      · exact hcs.2.2.1 e'
      · exact hcs.2.2.2 e')
    (fun i a hi => by
      have hm := insL_some P tf _ i a hi
      simp only [bmL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · rw [show i = 0 from Fin.ext e]; exact e0
      · rw [show i = 1 from Fin.ext e]; exact e1
      · rw [show i = 2 from Fin.ext e]; exact e2
      · rw [show i = 3 from Fin.ext e]; exact e3)
    H A hPr
    (fun i a hi => by
      have hm := insL_some P tf _ i a hi
      simp only [bmL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
      · rw [show i = 0 from Fin.ext e]; exact hpo
      · rw [show i = 1 from Fin.ext e]; exact hq
      · rw [show i = 2 from Fin.ext e]; exact hsy
      · rw [show i = 3 from Fin.ext e]; exact hax)
    (fun i hi => by
      have hn := insL_none P tf _ i hi
      have h0 := hn (0, poT) (by simp [bmL])
      have h1 := hn (1, qT) (by simp [bmL])
      have h2 := hn (2, syT) (by simp [bmL])
      have h3 := hn (3, axT) (by simp [bmL])
      have e : i = 4 := Fin.ext (by have := i.isLt; simp only at h0 h1 h2 h3; show i.val = 4; omega)
      subst e; rfl)
    hW
  refine ⟨A1, st, ?_, l, p⟩
  unfold bmO; rw [o 4]; exact e4

/-- **The constant's code** (base's fixed-word printer docked, no inputs). -/
theorem ccStageF (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A (k0 + 40)) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (fun _ => none) (k0 + 40) (hc4 tf m deg De Dt k0 h))
        (HierarchyFixedWord.machine (CWConst.constWord m))) (2 * (CWConst.constWord m).length + 2) H A H A' ∧
      A' (ccO P tf m deg De Dt k0 h) = CWConst.constWord m ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + 40) → A' y = A y) ∧
      PristineH P tf H A' (k0 + 40 + 2) := by
  have hr : ClockJoin.ReadyRun (HierarchyFixedWord.machine (CWConst.constWord m))
      (2 * (CWConst.constWord m).length + 2) (fun _ => [])
      ![CWConst.constWord m, List.replicate (CWConst.constWord m).length false] := by
    obtain ⟨r, hr, ht, hh, hs⟩ := HierarchyFixedWord.word_ready (CWConst.constWord m)
    exact ⟨r, hr, ht, hh, hs.le⟩
  obtain ⟨st, hsl, hlow, hpr⟩ := readyN P tf _ _ _ _ hr
    (fun _ => none) (k0 + 40) (hc4 tf m deg De Dt k0 h) (fun i j a hi => by simp at hi)
    (fun i a hi => by simp at hi) (fun j a hj => by simp at hj) H A hPr (fun i a hi => by simp at hi)
    (fun i _ => rfl)
  exact ⟨_, st, by unfold ccO; rw [hsl 0]; rfl, hlow, hpr⟩

/-- **A unary copy** (`ClockUnarySum.sum_ready v 0` docked): `1^v` at `a` kept, `1^v` on the stage's tape `2`. -/
theorem cpStage (v k : ℕ) (hk : k + 4 ≤ tf) (a : Fin (NW P tf)) (ha : 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k)
    (hv : A a = List.replicate v true ∧ H a = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf a) k hk) ClockUnarySum.machine) (2 * (v + 0) + 6) H A H A' ∧
      A' (sl P tf (sh1 P tf a) k hk (2 : Fin 4)) = List.replicate v true ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k → A' y = A y) ∧ PristineH P tf H A' (k + 4) := by
  obtain ⟨st, hsl, hlow, hpr⟩ := ready1 P tf _ _ _ _ (ClockUnarySum.sum_ready v 0)
    (fun j hj => by fin_cases j <;> simp_all)
    (fun j hj => by
      have e : j = 0 := Fin.ext hj
      subst e; rfl)
    k hk a ha H A hPr
    (fun j hj => by
      have e : j = 0 := Fin.ext hj
      subst e; exact hv.1) hv.2
  exact ⟨_, st, by rw [hsl]; simp, hlow, hpr⟩

end Stages

/-! ## The fold and the phase -/

section Fold
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (deg De Dt : ℕ) (k0 : ℕ) (h : k0 + CH5 m deg De Dt ≤ tf)
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

theorem insL_none_of {t : ℕ} (l : List (ℕ × Fin (NW P tf))) (i : Fin t) (hl : ∀ p ∈ l, p.1 ≠ i.val) :
    insL P tf l i = none := by
  unfold insL
  have e : l.find? (fun p => p.1 == i.val) = none :=
    List.find?_eq_none.mpr (fun p hp => by simpa using hl p hp)
  rw [e]; rfl

theorem hd_of_nodup (l : List (ℕ × Fin (NW P tf))) (hn : (l.map Prod.snd).Nodup) :
    ∀ p ∈ l, ∀ p' ∈ l, p.2 = p'.2 → p.1 = p'.1 := fun _ h1 _ h2 e =>
  congrArg Prod.fst (List.inj_on_of_nodup_map hn h1 h2 e)

/-- **The writers' fold** (`FrontFoldStage.stage_step` docked): every variable's parity code, carrier code and envelope
bit on the fold's kept tapes `5`, `6`, `7`; the count word and the two unary copies it reads may be consumed. -/
theorem foldStageF (Ce Ct q : ℕ) (F : FrontFoldLoop.FoldIn m q) (n0 Wa cw : ℕ)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ value Dt Ct n0)
    (henv : ∀ X < F.nv, FrontFoldLoop.EnvFit (F.car X) deg (value De Ce n0))
    (hcw : ∀ X < F.nv, FrontFoldLoop.rcost (PwM m) (CwM m) F (value De Ce n0) Wa X ≤ cw)
    (hcwT : cw + 1 ≤ value Dt Ct n0)
    (hlen : ∀ X ≤ F.nv, ∀ t,
      (F.st deg (value De Ce n0) (value Dt Ct n0) X (PwM m).t (CwM m).t t).length ≤ value Dt Ct n0)
    (b c y w u v : Fin (NW P tf)) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A (k0 + 50))
    (hl : ∀ p ∈ foL P tf m b c y w u v, 2 + NL P ≤ p.2.val ∧ p.2.val < 2 + NL P + (k0 + 50))
    (hd : ∀ p ∈ foL P tf m b c y w u v, ∀ p' ∈ foL P tf m b c y w u v, p.2 = p'.2 → p.1 = p'.1)
    (hb : A b = F.ys.flatMap frame ∧ H b = 0) (hc : A c = F.as.flatMap frame ∧ H c = 0)
    (hy : A y = List.replicate F.sys true ∧ H y = 0) (hw : A w = CompareMachine.word F.nv ∧ H w = 0)
    (hu : A u = List.replicate q true ∧ H u = 0) (hv : A v = List.replicate n0 true ∧ H v = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (insL P tf (foL P tf m b c y w u v)) (k0 + 50) (hc7 tf m deg De Dt k0 h))
        (FrontFoldStage.stageM (PwM m) (CwM m) deg De Ce Dt Ct))
        (FrontFoldStage.stageCost deg De Ce Dt Ct q n0 F.nv cw) H A H A' ∧
      A' (sl P tf (insL P tf (foL P tf m b c y w u v)) (k0 + 50) (hc7 tf m deg De Dt k0 h)
        ⟨5, by have := nsf_ge m deg De Dt; omega⟩) = ((List.range F.nv).map F.pw).flatMap frame ∧
      A' (sl P tf (insL P tf (foL P tf m b c y w u v)) (k0 + 50) (hc7 tf m deg De Dt k0 h)
        ⟨6, by have := nsf_ge m deg De Dt; omega⟩) = ((List.range F.nv).map F.cw).flatMap frame ∧
      A' (sl P tf (insL P tf (foL P tf m b c y w u v)) (k0 + 50) (hc7 tf m deg De Dt k0 h)
        ⟨7, by have := nsf_ge m deg De Dt; omega⟩) = (List.range F.nv).map (F.eb deg) ∧
      (∀ z : Fin (NW P tf), z.val < 2 + NL P + (k0 + 50) → z ≠ w → z ≠ u → z ≠ v → A' z = A z) ∧
      PristineH P tf H A' (k0 + 50 + NSF m deg De Dt) := by
  obtain ⟨out, hs, hout⟩ := FrontFoldStage.stage_step (PwM m) (CwM m) F deg De Ce Dt Ct n0 Wa cw hWa hZ0 henv hcw
    hcwT hlen
  have mem : ∀ (i : Fin (NSF m deg De Dt)) (a : Fin (NW P tf)), (i.val, a) ∈ foL P tf m b c y w u v →
      (i.val = 0 ∧ a = b) ∨ (i.val = 2 ∧ a = c) ∨ (i.val = 4 ∧ a = y) ∨
        (i.val = 1220 + (PwM m).t + (CwM m).t + 2 ∧ a = w) ∨ (i.val = 1220 + (PwM m).t + (CwM m).t + 3 ∧ a = u) ∨
          (i.val = 1220 + (PwM m).t + (CwM m).t + 4 ∧ a = v) := by
    intro i a hm
    simpa only [foL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] using hm
  obtain ⟨st, hsl, hlow, hpr⟩ := stepK P tf _ _ _ out hs (insL P tf (foL P tf m b c y w u v)) (k0 + 50)
    (hc7 tf m deg De Dt k0 h) (insL_inj P tf _ hd) (insL_low P tf _ _ hl) H A hPr
    (fun i a hi => by
      rcases mem i a (insL_some P tf _ i a hi) with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
      · refine ⟨?_, hb.2⟩; rw [hb.1]; simp only [FrontFoldStage.stIn]; rw [if_pos e]
      · refine ⟨?_, hc.2⟩; rw [hc.1]; simp only [FrontFoldStage.stIn]; rw [if_neg (by omega), if_pos e]
      · refine ⟨?_, hy.2⟩; rw [hy.1]; simp only [FrontFoldStage.stIn]
        rw [if_neg (by omega), if_neg (by omega), if_pos e]
      · refine ⟨?_, hw.2⟩; rw [hw.1]; simp only [FrontFoldStage.stIn]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
      · refine ⟨?_, hu.2⟩; rw [hu.1]; simp only [FrontFoldStage.stIn]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
      · refine ⟨?_, hv.2⟩; rw [hv.1]; simp only [FrontFoldStage.stIn]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e])
    (fun i hi => by
      have hn := insL_none P tf _ i hi
      have h0 := hn (0, b) (by simp [foL])
      have h2 := hn (2, c) (by simp [foL])
      have h4 := hn (4, y) (by simp [foL])
      have h5 := hn (1220 + (PwM m).t + (CwM m).t + 2, w) (by simp [foL])
      have h6 := hn (1220 + (PwM m).t + (CwM m).t + 3, u) (by simp [foL])
      have h7 := hn (1220 + (PwM m).t + (CwM m).t + 4, v) (by simp [foL])
      simp only at h0 h2 h4 h5 h6 h7
      simp only [FrontFoldStage.stIn]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)])
  have g : ∀ (j : ℕ) (hj : j < 10), install (sl P tf (insL P tf (foL P tf m b c y w u v)) (k0 + 50)
      (hc7 tf m deg De Dt k0 h)) A out (sl P tf (insL P tf (foL P tf m b c y w u v)) (k0 + 50) (hc7 tf m deg De Dt k0 h)
        ⟨j, by have := nsf_ge m deg De Dt; omega⟩) =
      F.st deg (value De Ce n0) (value Dt Ct n0) F.nv (PwM m).t (CwM m).t ⟨j, by omega⟩ :=
    fun j hj => (hsl _).trans (hout _ hj)
  refine ⟨_, st, ?_, ?_, ?_, fun z hz h1 h2 h3 => hlow z hz (fun j hj => ?_), hpr⟩
  · rw [g 5 (by norm_num)]; simp [FrontFoldLoop.FoldIn.st, FrontFoldRound.Qf]
  · rw [g 6 (by norm_num)]; simp [FrontFoldLoop.FoldIn.st, FrontFoldRound.Qf]
  · rw [g 7 (by norm_num)]; simp [FrontFoldLoop.FoldIn.st, FrontFoldRound.Qf]
  · rcases mem j z (insL_some P tf _ j z hj) with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
    · rw [hout j (by omega)]
      simp [FrontFoldLoop.FoldIn.st, FrontFoldRound.Qf, FrontFoldStage.stIn, e]
    · rw [hout j (by omega)]
      simp [FrontFoldLoop.FoldIn.st, FrontFoldRound.Qf, FrontFoldStage.stIn, e]
    · rw [hout j (by omega)]
      simp [FrontFoldLoop.FoldIn.st, FrontFoldRound.Qf, FrontFoldStage.stIn, e]
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h3

end Fold

/-! ## Phase 5 composed -/

/-- The phase's inputs are distinct where its stages share them. -/
structure Dist5 {N : ℕ} (rT poT qT cT sT syT axT nvT nwT : Fin N) : Prop where
  rc : rT ≠ cT
  rn : rT ≠ nvT
  rs : rT ≠ sT
  ns : nvT ≠ sT
  cn : cT ≠ nvT
  cs : cT ≠ sT
  pq : poT ≠ qT
  py : poT ≠ syT
  pa : poT ≠ axT
  qy : qT ≠ syT
  qa : qT ≠ axT
  ya : syT ≠ axT
  cp : cT ≠ poT
  cq : cT ≠ qT
  cy : cT ≠ syT
  ca : cT ≠ axT
  yw : syT ≠ nwT

/-- **Phase 5's cost.** -/
noncomputable def ch5Cost (m : Mode) (W r s Wn nv q sys aux cb n0 deg De Ce Dt Ct fnv cw : ℕ) : ℕ :=
  ((11 * W + 20) + 1 + (1 + 1 + (2 * (10 * r + 1) + 2))) + 1 +
  (((11 * W + 20) + 1 + (1 + 1 + (2 * FrontFmtCA.caCost s Wn nv + 2))) + 1 +
  (((11 * W + 20) + 1 + (1 + 1 + (2 * FrontFmtBM.bmCost q sys aux cb + 2))) + 1 +
  ((2 * (CWConst.constWord m).length + 2) + 1 +
  ((2 * (q + 0) + 6) + 1 + ((2 * (n0 + 0) + 6) + 1 +
    FrontFoldStage.stageCost deg De Ce Dt Ct q n0 fnv cw)))))

section Phase
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (deg De Dt : ℕ) (k0 : ℕ) (h : k0 + CH5 m deg De Dt ≤ tf)
  (rT poT qT cT sT syT axT nvT nwT n0T : Fin (NW P tf))
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3P (sTape_val')

theorem unT_val : (unT P tf m deg De Dt k0 h rT cT).val = 2 + NL P + (k0 + 2) := by
  unfold unT; rw [stT_none P tf _ _ _ _ 1 (sh1_ne P tf rT _ (by decide)), sTape_val' (1 : Fin 2) (by decide)]; rfl

theorem caO_val : (caO P tf m deg De Dt k0 h rT cT sT nvT).val = 2 + NL P + (k0 + 6 + 4) := by
  unfold caO
  rw [stT_none P tf _ _ _ _ 3 (insL_none_of P tf _ _ (by
    intro p hp; simp only [caL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (dsimp only; decide))), sTape_val' (3 : Fin 4) (by decide)]; rfl

theorem bmO_val : (bmO P tf m deg De Dt k0 h poT qT cT syT axT).val = 2 + NL P + (k0 + 21 + 5) := by
  unfold bmO
  rw [stT_none P tf _ _ _ _ 4 (insL_none_of P tf _ _ (by
    intro p hp; simp only [bmL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (dsimp only; decide))), sTape_val' (4 : Fin 5) (by decide)]; rfl

theorem ccO_val : (ccO P tf m deg De Dt k0 h).val = 2 + NL P + (k0 + 40 + 0) := by
  unfold ccO; rw [sl_none P tf _ _ _ _ rfl, rg_val]; rfl

theorem qcT_val : (qcT P tf m deg De Dt k0 h qT).val = 2 + NL P + (k0 + 42 + 2) := by
  unfold qcT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf qT _ (by decide)), rg_val]; rfl

theorem ncT_val : (ncT P tf m deg De Dt k0 h n0T).val = 2 + NL P + (k0 + 46 + 2) := by
  unfold ncT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf n0T _ (by decide)), rg_val]; rfl

theorem fiT_val (j : ℕ) (hj : j < 10) (hj4 : 4 < j) :
    (fiT P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T j hj).val = 2 + NL P + (k0 + 50 + j) := by
  unfold fiT foIns
  rw [sl_none P tf _ _ _ _ (insL_none_of P tf _ _ (by
    intro p hp; simp only [foL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega))), rg_val]

set_option maxHeartbeats 1000000 in
/-- **Phase 5** (the seven stages composed): the raw rest, the constant's code, the parity codes, the carrier codes and
the envelope bits of all variables; the tapes below the phase kept except the count word, the tapes past it blank. -/
theorem ch5_step (es : List (Bool × Bool × ℕ)) (tail : List Bool) (s Wn q sys aux cb W n0 Ce Ct Wa cw : ℕ)
    (sb rest : List Bool) (F : FrontFoldLoop.FoldIn m q)
    (hes : (sys + aux) * s ≤ es.length) (hWn : ∀ e < es.length, (natWord (FrontFmtCA.codeE es e)).length ≤ Wn)
    (hcapC : (sys + aux + 1) * (2 * (s * Wn) + 2 * Wn + 3) + s + (sys + aux) ≤ 2 * W + 2)
    (hsb : sb.length = sys * q) (hcapB1 : (sys + aux + 1) * (2 * q + 1) + q + sys + aux + 1 ≤ 2 * W + 2)
    (hcapB2 : natBitLength 3 + natBitLength sys + natBitLength aux + natBitLength cb + 1 ≤ 2 * W + 2)
    (hWa : ∀ a ∈ F.as, a.length ≤ Wa) (hZ0 : F.nv + 1 ≤ value Dt Ct n0)
    (henv : ∀ X < F.nv, FrontFoldLoop.EnvFit (F.car X) deg (value De Ce n0))
    (hcw : ∀ X < F.nv, FrontFoldLoop.rcost (PwM m) (CwM m) F (value De Ce n0) Wa X ≤ cw)
    (hcwT : cw + 1 ≤ value Dt Ct n0)
    (hlen : ∀ X ≤ F.nv, ∀ t,
      (F.st deg (value De Ce n0) (value Dt Ct n0) X (PwM m).t (CwM m).t t).length ≤ value Dt Ct n0)
    (hys : (FrontFmtBM.rows q sb sys ++ List.replicate aux (List.replicate q false)).flatMap frame =
      F.ys.flatMap frame)
    (has : FrontFmtCA.itemsOf es s (sys + aux) = F.as.flatMap frame) (hFs : F.sys = sys) (hFn : F.nv = sys + aux)
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H A k0)
    (hLo : ∀ y ∈ [rT, poT, qT, cT, sT, syT, axT, nvT, nwT, n0T], 2 + NL P ≤ y.val ∧ y.val < 2 + NL P + k0)
    (hD : Dist5 rT poT qT cT sT syT axT nvT nwT)
    (hr : A rT = frame (FrontTW.entsW es ++ tail) ∧ H rT = 0)
    (hpo : A poT = FrontFmtBM.hdrOf sys aux cb ++ sb ++ rest ∧ H poT = 0)
    (hq : A qT = List.replicate q true ∧ H qT = 0) (hW : A cT = List.replicate W true ∧ H cT = 0)
    (hs : A sT = List.replicate s true ∧ H sT = 0) (hsy : A syT = List.replicate sys true ∧ H syT = 0)
    (hax : A axT = List.replicate aux true ∧ H axT = 0)
    (hnv : A nvT = List.replicate (sys + aux) true ∧ H nvT = 0)
    (hnw : A nwT = CompareMachine.word (sys + aux) ∧ H nwT = 0)
    (hn0 : A n0T = List.replicate n0 true ∧ H n0T = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (ch5M P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T Ce Ct)
        (ch5Cost m W (FrontTW.entsW es ++ tail).length s Wn (sys + aux) q sys aux cb n0 deg De Ce Dt Ct F.nv cw)
        H A H A' ∧
      A' (unT P tf m deg De Dt k0 h rT cT) = FrontTW.entsW es ++ tail ∧
      A' (ccO P tf m deg De Dt k0 h) = CWConst.constWord m ∧
      A' (fiT P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T 5 (by norm_num)) =
        ((List.range F.nv).map F.pw).flatMap frame ∧
      A' (fiT P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T 6 (by norm_num)) =
        ((List.range F.nv).map F.cw).flatMap frame ∧
      A' (fiT P tf m deg De Dt k0 h rT poT qT cT sT syT axT nvT nwT n0T 7 (by norm_num)) =
        (List.range F.nv).map (F.eb deg) ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → y ≠ nwT → A' y = A y) ∧
      PristineH P tf H A' (k0 + CH5 m deg De Dt) := by
  have lr := hLo rT (by simp)
  have lp := hLo poT (by simp)
  have lq := hLo qT (by simp)
  have lc := hLo cT (by simp)
  have ls := hLo sT (by simp)
  have ly := hLo syT (by simp)
  have la := hLo axT (by simp)
  have ln := hLo nvT (by simp)
  have lw := hLo nwT (by simp)
  have l0 := hLo n0T (by simp)
  have vU := unT_val P tf m deg De Dt k0 h rT cT
  have vC := caO_val P tf m deg De Dt k0 h rT cT sT nvT
  have vB := bmO_val P tf m deg De Dt k0 h poT qT cT syT axT
  have vK := ccO_val P tf m deg De Dt k0 h
  have vQ := qcT_val P tf m deg De Dt k0 h qT
  have vN := ncT_val P tf m deg De Dt k0 h n0T
  have e1 : k0 + WT 1 0 = k0 + 6 := rfl
  have e2 : k0 + 6 + WT 3 7 = k0 + 21 := by unfold WT; omega
  have e3 : k0 + 21 + WT 4 10 = k0 + 40 := by unfold WT; omega
  have e4 : k0 + 40 + 2 = k0 + 42 := by omega
  have e5 : k0 + 42 + 4 = k0 + 46 := by omega
  have e6 : k0 + 46 + 4 = k0 + 50 := by omega
  have e7 : k0 + 50 + NSF m deg De Dt = k0 + CH5 m deg De Dt := by unfold CH5; omega
  -- 1. the raw rest
  obtain ⟨A1, s1, w1, l1, p1⟩ := unStageF P tf m deg De Dt k0 h rT cT (FrontTW.entsW es ++ tail) W H A hPr lr lc
    hD.rc hr hW
  rw [e1] at p1
  -- 2. the atoms' codes
  obtain ⟨A2, s2, w2, l2, p2⟩ := caStageF P tf m deg De Dt k0 h rT cT sT nvT es tail s Wn (sys + aux) W hes hWn hcapC
    H A1 p1
    (fun p hp => by
      simp only [caL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨lr.1, by dsimp only; omega⟩
      · exact ⟨ln.1, by dsimp only; omega⟩
      · exact ⟨ls.1, by dsimp only; omega⟩)
    (hd_of_nodup P tf _ (by simp [caL, hD.rn, hD.rs, hD.ns]))
    ⟨lc.1, by omega⟩ ⟨hD.rc.symm, hD.cn, hD.cs⟩
    ⟨by rw [l1 rT (by omega)]; exact hr.1, hr.2⟩ ⟨by rw [l1 nvT (by omega)]; exact hnv.1, hnv.2⟩
    ⟨by rw [l1 sT (by omega)]; exact hs.1, hs.2⟩ ⟨by rw [l1 cT (by omega)]; exact hW.1, hW.2⟩
  rw [e2] at p2
  -- 3. the bitmaps
  obtain ⟨A3, s3, w3, l3, p3⟩ := bmStageF P tf m deg De Dt k0 h poT qT cT syT axT q sys aux cb W sb rest hsb hcapB1
    hcapB2 H A2 p2
    (fun p hp => by
      simp only [bmL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨lp.1, by dsimp only; omega⟩
      · exact ⟨lq.1, by dsimp only; omega⟩
      · exact ⟨ly.1, by dsimp only; omega⟩
      · exact ⟨la.1, by dsimp only; omega⟩)
    (hd_of_nodup P tf _ (by simp [bmL, hD.pq, hD.py, hD.pa, hD.qy, hD.qa, hD.ya]))
    ⟨lc.1, by omega⟩ ⟨hD.cp, hD.cq, hD.cy, hD.ca⟩
    ⟨by rw [l2 poT (by omega), l1 poT (by omega)]; exact hpo.1, hpo.2⟩
    ⟨by rw [l2 qT (by omega), l1 qT (by omega)]; exact hq.1, hq.2⟩
    ⟨by rw [l2 syT (by omega), l1 syT (by omega)]; exact hsy.1, hsy.2⟩
    ⟨by rw [l2 axT (by omega), l1 axT (by omega)]; exact hax.1, hax.2⟩
    ⟨by rw [l2 cT (by omega), l1 cT (by omega)]; exact hW.1, hW.2⟩
  rw [e3] at p3
  -- 4. the constant's code
  obtain ⟨A4, s4, w4, l4, p4⟩ := ccStageF P tf m deg De Dt k0 h H A3 p3
  rw [e4] at p4
  -- 5, 6. the copies
  obtain ⟨A5, s5, w5, l5, p5⟩ := cpStage P tf q (k0 + 42) (hc5 tf m deg De Dt k0 h) qT ⟨lq.1, by omega⟩ H A4 p4
    ⟨by rw [l4 qT (by omega), l3 qT (by omega), l2 qT (by omega), l1 qT (by omega)]; exact hq.1, hq.2⟩
  rw [e5] at p5
  obtain ⟨A6, s6, w6, l6, p6⟩ := cpStage P tf n0 (k0 + 46) (hc6 tf m deg De Dt k0 h) n0T ⟨l0.1, by omega⟩ H A5 p5
    ⟨by
      rw [l5 n0T (by omega), l4 n0T (by omega), l3 n0T (by omega), l2 n0T (by omega), l1 n0T (by omega)]
      exact hn0.1, hn0.2⟩
  rw [e6] at p6
  -- 7. the fold
  have L6 : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A6 y = A y := fun y hy => by
    rw [l6 y (by omega), l5 y (by omega), l4 y (by omega), l3 y (by omega), l2 y (by omega), l1 y (by omega)]
  obtain ⟨A7, s7, f5, f6, f7, l7, p7⟩ := foldStageF P tf m deg De Dt k0 h Ce Ct q F n0 Wa cw hWa hZ0 henv hcw hcwT
    hlen (bmO P tf m deg De Dt k0 h poT qT cT syT axT) (caO P tf m deg De Dt k0 h rT cT sT nvT) syT nwT
    (qcT P tf m deg De Dt k0 h qT) (ncT P tf m deg De Dt k0 h n0T) H A6 p6
    (fun p hp => by
      simp only [foL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨ly.1, by dsimp only; omega⟩
      · exact ⟨lw.1, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (hd_of_nodup P tf _ (by
      show ([bmO P tf m deg De Dt k0 h poT qT cT syT axT, caO P tf m deg De Dt k0 h rT cT sT nvT, syT, nwT, qcT P tf m deg De Dt k0 h qT, ncT P tf m deg De Dt k0 h n0T] : List (Fin (NW P tf))).Nodup
      have n12 : (bmO P tf m deg De Dt k0 h poT qT cT syT axT) ≠ (caO P tf m deg De Dt k0 h rT cT sT nvT) := fun e => by have ev := congrArg Fin.val e; rw [vB, vC] at ev; omega
      have n13 : (bmO P tf m deg De Dt k0 h poT qT cT syT axT) ≠ syT := fun e => by have ev := congrArg Fin.val e; rw [vB] at ev; omega
      have n14 : (bmO P tf m deg De Dt k0 h poT qT cT syT axT) ≠ nwT := fun e => by have ev := congrArg Fin.val e; rw [vB] at ev; omega
      have n15 : (bmO P tf m deg De Dt k0 h poT qT cT syT axT) ≠ (qcT P tf m deg De Dt k0 h qT) := fun e => by have ev := congrArg Fin.val e; rw [vB, vQ] at ev; omega
      have n16 : (bmO P tf m deg De Dt k0 h poT qT cT syT axT) ≠ (ncT P tf m deg De Dt k0 h n0T) := fun e => by have ev := congrArg Fin.val e; rw [vB, vN] at ev; omega
      have n23 : (caO P tf m deg De Dt k0 h rT cT sT nvT) ≠ syT := fun e => by have ev := congrArg Fin.val e; rw [vC] at ev; omega
      have n24 : (caO P tf m deg De Dt k0 h rT cT sT nvT) ≠ nwT := fun e => by have ev := congrArg Fin.val e; rw [vC] at ev; omega
      have n25 : (caO P tf m deg De Dt k0 h rT cT sT nvT) ≠ (qcT P tf m deg De Dt k0 h qT) := fun e => by have ev := congrArg Fin.val e; rw [vC, vQ] at ev; omega
      have n26 : (caO P tf m deg De Dt k0 h rT cT sT nvT) ≠ (ncT P tf m deg De Dt k0 h n0T) := fun e => by have ev := congrArg Fin.val e; rw [vC, vN] at ev; omega
      have n35 : syT ≠ (qcT P tf m deg De Dt k0 h qT) := fun e => by have ev := congrArg Fin.val e; rw [vQ] at ev; omega
      have n36 : syT ≠ (ncT P tf m deg De Dt k0 h n0T) := fun e => by have ev := congrArg Fin.val e; rw [vN] at ev; omega
      have n45 : nwT ≠ (qcT P tf m deg De Dt k0 h qT) := fun e => by have ev := congrArg Fin.val e; rw [vQ] at ev; omega
      have n46 : nwT ≠ (ncT P tf m deg De Dt k0 h n0T) := fun e => by have ev := congrArg Fin.val e; rw [vN] at ev; omega
      have n56 : (qcT P tf m deg De Dt k0 h qT) ≠ (ncT P tf m deg De Dt k0 h n0T) := fun e => by have ev := congrArg Fin.val e; rw [vQ, vN] at ev; omega
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
        not_false_eq_true]
      exact ⟨⟨n12, n13, n14, n15, n16⟩, ⟨n23, n24, n25, n26⟩, ⟨hD.yw, n35, n36⟩, ⟨n45, n46⟩, n56⟩))
    ⟨by
      rw [l6 (bmO P tf m deg De Dt k0 h poT qT cT syT axT) (by omega), l5 (bmO P tf m deg De Dt k0 h poT qT cT syT axT) (by omega), l4 (bmO P tf m deg De Dt k0 h poT qT cT syT axT) (by omega), w3]; exact hys,
      (hPr.1 (bmO P tf m deg De Dt k0 h poT qT cT syT axT) (by omega)).2⟩
    ⟨by
      rw [l6 (caO P tf m deg De Dt k0 h rT cT sT nvT) (by omega), l5 (caO P tf m deg De Dt k0 h rT cT sT nvT) (by omega), l4 (caO P tf m deg De Dt k0 h rT cT sT nvT) (by omega), l3 (caO P tf m deg De Dt k0 h rT cT sT nvT) (by omega), w2]
      exact has, (hPr.1 (caO P tf m deg De Dt k0 h rT cT sT nvT) (by omega)).2⟩
    ⟨by rw [L6 syT ly.2, hFs]; exact hsy.1, hsy.2⟩
    ⟨by rw [L6 nwT lw.2, hFn]; exact hnw.1, hnw.2⟩
    ⟨by rw [l6 (qcT P tf m deg De Dt k0 h qT) (by omega)]; exact w5, (hPr.1 (qcT P tf m deg De Dt k0 h qT) (by omega)).2⟩
    ⟨w6, (hPr.1 (ncT P tf m deg De Dt k0 h n0T) (by omega)).2⟩
  rw [e7] at p7
  have ne3 : ∀ y : Fin (NW P tf), 2 + NL P + k0 ≤ y.val → y.val < 2 + NL P + (k0 + 42) →
      y ≠ nwT ∧ y ≠ qcT P tf m deg De Dt k0 h qT ∧ y ≠ ncT P tf m deg De Dt k0 h n0T := fun y h1 h2 =>
    ⟨fun e => by rw [e] at h1; omega, fun e => by rw [e, vQ] at h2; omega, fun e => by rw [e, vN] at h2; omega⟩
  refine ⟨A7, ?_, ?_, ?_, f5, f6, f7, fun y hy hyw => ?_, p7⟩
  · unfold ch5M ch5Cost
    exact Step.seq s1 (Step.seq s2 (Step.seq s3 (Step.seq s4 (Step.seq s5 (Step.seq s6 s7)))))
  · obtain ⟨a1, a2, a3⟩ := ne3 (unT P tf m deg De Dt k0 h rT cT) (by omega) (by omega)
    rw [l7 (unT P tf m deg De Dt k0 h rT cT) (by omega) a1 a2 a3, l6 (unT P tf m deg De Dt k0 h rT cT) (by omega),
      l5 (unT P tf m deg De Dt k0 h rT cT) (by omega), l4 (unT P tf m deg De Dt k0 h rT cT) (by omega),
      l3 (unT P tf m deg De Dt k0 h rT cT) (by omega), l2 (unT P tf m deg De Dt k0 h rT cT) (by omega)]
    exact w1
  · obtain ⟨a1, a2, a3⟩ := ne3 (ccO P tf m deg De Dt k0 h) (by omega) (by omega)
    rw [l7 (ccO P tf m deg De Dt k0 h) (by omega) a1 a2 a3, l6 (ccO P tf m deg De Dt k0 h) (by omega),
      l5 (ccO P tf m deg De Dt k0 h) (by omega)]
    exact w4
  · have a2 : y ≠ qcT P tf m deg De Dt k0 h qT := fun e => by rw [e, vQ] at hy; omega
    have a3 : y ≠ ncT P tf m deg De Dt k0 h n0T := fun e => by rw [e, vN] at hy; omega
    rw [l7 y (by omega) hyw a2 a3, L6 y hy]

end Phase

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCh5
