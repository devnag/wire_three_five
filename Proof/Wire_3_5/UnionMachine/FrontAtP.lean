import Proof.Wire_3_5.UnionMachine.FrontCh5
import Proof.Wire_3_5.UnionMachine.FrontAtomStageL

/-! # C6 front, the chain: the atom test docked (P3:3669-3674, 3092-3094)

After the entries' check, the atom stage (`FrontAtomStageL.atoms_stage`: every atom decodes and has at most
`L = (q+1)^{descDeg}` description bits iff its verdict is `0`) runs on copies of the rest `frame r` (base's witness
copy), of `1^q` and of `1^E`, and on phase 3's dedicated `1^{|x|}` (twice) and `1^L`. **`frStage`** (a framed word's
copy docked), **`atP_step`**: the verdict register `regTape (2nf+2) v` with its head at `v`, the tapes below the phase
kept except the three dedicated counts, the tapes past it blank.

Paper quantity of the main type: the atom test's verdict (decode ∧ AtomsOkG at the envelope, P3:3092-3094). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtP
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCh3 NearCubicWires.WireExponent3_5.UnionMachine.FrontCh5

/-- The atom stage's hypotheses on the rest `r` (entries, payloads, capacities), bundled. -/
structure AtomsOK (r : List Bool) (nw q E nf : ℕ) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (Kc Kd : ℕ) : Prop where
  hE : 1 ≤ E
  hpos0 : pos 0 = 0
  hent : ∀ j, j < E → ∃ b x rest, r.drop (pos j) =
    FrontEntriesRef.gridWord b x ++ (List.replicate (pay j).length true ++ false :: pay j) ++ rest
  hk : ∀ j, j < E → 1 ≤ (pay j).length
  hpos : ∀ j, j < E → pos (j + 1) = pos j + 2 * (pay j).length + 5
  hP : ∀ j, j < E → 2 * (pay j).length + 1 ≤ FrontAtomStageL.capP nw
  hC : ∀ j, j < E → CloseoutRowsCircuitCapacity.capacity (pay j).length ≤ FrontAtomStageL.capP nw
  hcap : ∀ j, j < E → 2 * (pos j + 2 * (pay j).length + 5) + 2 ≤ 2 * nf + 2
  hq : q + 3 ≤ 2 * nf + 2
  hEc : E + 1 ≤ 2 * nf + 2
  hKc : ∀ j, j < E → 70 * ((pay j).length + 2) ≤ Kc
  hKd : ∀ j, j < E → CloseoutRowsCircuitWholeBudget.budget (FrontAtomStageL.capP nw) (pay j).length ≤ Kd

section Copy
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- **A framed word's copy** (base's witness copy) docked: `frame r` at `a` kept, `frame r` on the stage's tape `1`. -/
theorem frStage (r : List Bool) (k : ℕ) (hk : k + 4 ≤ tf) (a : Fin (NW P tf))
    (ha : 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k) (hr : A a = frame r ∧ H a = 0) :
    ∃ A' : Fin (NW P tf) → List Bool,
      Step (RecoveryFocus.machine (sl P tf (sh1 P tf a) k hk) RecoveryColdWitnessCopy.machine) (8 * r.length + 14)
        H A H A' ∧
      A' (sl P tf (sh1 P tf a) k hk (1 : Fin 4)) = frame r ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k → A' y = A y) ∧ PristineH P tf H A' (k + 4) := by
  obtain ⟨st, hsl, hlow, hpr⟩ := stepK P tf _ _ _ _ (step_of_rready (RecoveryColdWitnessCopy.copy_ready r))
    (sh1 P tf a) k hk (sh1_I P tf a) (sh1_L P tf a k ha) H A hPr
    (fun i b hi => by
      unfold sh1 at hi; split_ifs at hi with h0
      have e : i = 0 := Fin.ext h0
      subst e; rw [← Option.some.inj hi]; exact hr)
    (fun i hi => by
      unfold sh1 at hi; split_ifs at hi with h0
      fin_cases i <;> simp_all [RecoveryColdWitnessCopy.input])
  refine ⟨_, st, by rw [hsl]; rfl, fun y hy => hlow y hy (fun j hj => ?_), hpr⟩
  unfold sh1 at hj; split_ifs at hj with h0
  have e : j = 0 := Fin.ext h0
  subst e; rfl

end Copy

/-! ## The phase -/

section Phase
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- The phase's size: three copies, the atom stage. -/
abbrev AP : ℕ := 12 + FrontAtomStageL.ST

theorem sIn_eq (r : List Bool) (nw q E nf L : ℕ) (i : Fin FrontAtomStageL.ST) :
    FrontAtomStageL.sIn r nw q E nf L i =
      if i.val = 1703 then frame r else if i.val = 1780 then List.replicate nw true
      else if i.val = 1781 then List.replicate q true else if i.val = 1782 then List.replicate E true
      else if i.val = 1783 then List.replicate nf true else if i.val = 1793 then List.replicate L true else [] := by
  unfold FrontAtomStageL.sIn
  simp only [Fin.ext_iff, FrontAtomStageL.lp_val, FrontAtomStageL.xs_val, FrontAtomStageL.sm_val]
  rfl

variable (k0 : ℕ) (h : k0 + AP ≤ tf)

include h in
theorem ha1 : k0 + 4 ≤ tf := by unfold AP at h; omega
include h in
theorem ha2 : (k0 + 4) + 4 ≤ tf := by unfold AP at h; omega
include h in
theorem ha3 : (k0 + 8) + 4 ≤ tf := by unfold AP at h; omega
include h in
theorem ha4 : (k0 + 12) + FrontAtomStageL.ST ≤ tf := by unfold AP at h; omega

variable (rT x1T qT eT x2T lT : Fin (NW P tf))

/-- The copies of `frame r`, `1^q`, `1^E`. -/
noncomputable def rcT : Fin (NW P tf) := sl P tf (sh1 P tf rT) k0 (ha1 tf k0 h) (1 : Fin 4)
noncomputable def qcT : Fin (NW P tf) := sl P tf (sh1 P tf qT) (k0 + 4) (ha2 tf k0 h) (2 : Fin 4)
noncomputable def ecT : Fin (NW P tf) := sl P tf (sh1 P tf eT) (k0 + 8) (ha3 tf k0 h) (2 : Fin 4)

/-- The atom stage's shared inputs: the rest's copy, `1^{|x|}`, `1^q`'s copy, `1^E`'s copy, `1^{|x|}`, `1^L`. -/
noncomputable def atL : List (ℕ × Fin (NW P tf)) :=
  [(1703, rcT P tf k0 h rT), (1780, x1T), (1781, qcT P tf k0 h qT), (1782, ecT P tf k0 h eT), (1783, x2T), (1793, lT)]

/-- **The phase's machine.** -/
noncomputable def atM (m : Mode) :=
  Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf rT) k0 (ha1 tf k0 h)) RecoveryColdWitnessCopy.machine)
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf qT) (k0 + 4) (ha2 tf k0 h)) ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf eT) (k0 + 8) (ha3 tf k0 h)) ClockUnarySum.machine)
    (RecoveryFocus.machine (sl P tf (insL P tf (atL P tf k0 h rT x1T qT eT x2T lT)) (k0 + 12) (ha4 tf k0 h))
      (FrontAtomStageL.stageM m))))

/-- The verdict's register tape. -/
noncomputable def vtT : Fin (NW P tf) :=
  sl P tf (insL P tf (atL P tf k0 h rT x1T qT eT x2T lT)) (k0 + 12) (ha4 tf k0 h)
    (FrontAtomStageL.lp (FrontAtomLayout.sm 7))

theorem rcT_val : (rcT P tf k0 h rT).val = 2 + NL P + (k0 + 1) := by
  unfold rcT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf rT _ (by decide)), rg_val]; rfl
theorem qcT_val : (qcT P tf k0 h qT).val = 2 + NL P + (k0 + 4 + 2) := by
  unfold qcT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf qT _ (by decide)), rg_val]; rfl
theorem ecT_val : (ecT P tf k0 h eT).val = 2 + NL P + (k0 + 8 + 2) := by
  unfold ecT; rw [sl_none P tf _ _ _ _ (sh1_ne P tf eT _ (by decide)), rg_val]; rfl

/-- The phase's fuel. -/
noncomputable def atCost (m : Mode) (r : List Bool) (nw q E nf L Kc Kd : ℕ) (pay : ℕ → List Bool) : ℕ :=
  (8 * r.length + 14) + 1 + ((2 * (q + 0) + 6) + 1 + ((2 * (E + 0) + 6) + 1 +
    (FrontAtomStageL.setupCost nw nf L + 1 + (40 * (q + 2) + 1 + ((20 * E + 20) + 1 +
      (FrontAtomLoop.roundsOf q (FrontAtomStageL.capP nw) L m E pay *
        (FrontAtomLoop.roundCost (FrontAtomStageL.capP nw) (FrontAtomStageL.capP nw + FrontAtomStageL.capP nw) Kc Kd
          + 2) + 1))))))

/-- **The atom test in the chain**: the verdict register `regTape (2nf+2) v` at its head `v` (`v = 0` iff every atom
decodes and has at most `L` description bits); the tapes below the phase kept except the dedicated counts `1^{|x|}`
(twice) and `1^L`; the tapes past it blank. -/
theorem atP_step (m : Mode) (r : List Bool) (nw q E nf L : ℕ) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (Kc Kd : ℕ)
    (hA : AtomsOK r nw q E nf pos pay Kc Kd) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hLo : ∀ y ∈ [rT, x1T, qT, eT, x2T, lT], 2 + NL P ≤ y.val ∧ y.val < 2 + NL P + k0)
    (h12 : x1T ≠ x2T) (h1l : x1T ≠ lT) (h2l : x2T ≠ lT)
    (hr : A rT = frame r ∧ H rT = 0) (hx1 : A x1T = List.replicate nw true ∧ H x1T = 0)
    (hq : A qT = List.replicate q true ∧ H qT = 0) (he : A eT = List.replicate E true ∧ H eT = 0)
    (hx2 : A x2T = List.replicate nf true ∧ H x2T = 0) (hl : A lT = List.replicate L true ∧ H lT = 0) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (atM P tf k0 h rT x1T qT eT x2T lT m) (atCost m r nw q E nf L Kc Kd pay) H A H' A' ∧
      A' (vtT P tf k0 h rT x1T qT eT x2T lT) =
        regTape (2 * nf + 2) (FrontAtomLoop.verdictOf q (FrontAtomStageL.capP nw) L m E pay) ∧
      H' (vtT P tf k0 h rT x1T qT eT x2T lT) = FrontAtomLoop.verdictOf q (FrontAtomStageL.capP nw) L m E pay ∧
      (∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → y ≠ x1T → y ≠ x2T → y ≠ lT → A' y = A y ∧ H' y = H y) ∧
      PristineH P tf H' A' (k0 + AP) := by
  have lr := hLo rT (by simp)
  have l1' := hLo x1T (by simp)
  have lq := hLo qT (by simp)
  have le := hLo eT (by simp)
  have l2' := hLo x2T (by simp)
  have ll := hLo lT (by simp)
  have vR := rcT_val P tf k0 h rT
  have vQ := qcT_val P tf k0 h qT
  have vE := ecT_val P tf k0 h eT
  -- 1-3. the copies
  obtain ⟨A1, s1, w1, m1, p1⟩ := frStage P tf r k0 (ha1 tf k0 h) rT lr H A hPr hr
  obtain ⟨A2, s2, w2, m2, p2⟩ := cpStage P tf q (k0 + 4) (ha2 tf k0 h) qT ⟨lq.1, by omega⟩ H A1 p1
    ⟨by rw [m1 qT (by omega)]; exact hq.1, hq.2⟩
  obtain ⟨A3, s3, w3, m3, p3⟩ := cpStage P tf E (k0 + 8) (ha3 tf k0 h) eT ⟨le.1, by omega⟩ H A2 p2
    ⟨by rw [m2 eT (by omega), m1 eT (by omega)]; exact he.1, he.2⟩
  have L3 : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A3 y = A y := fun y hy => by
    rw [m3 y (by omega), m2 y (by omega), m1 y (by omega)]
  -- 4. the atom stage
  obtain ⟨Ha, Aa, hS, hv, hh⟩ := FrontAtomStageL.atoms_stage r nw q E nf L m hA.hE pos pay hA.hpos0 hA.hent hA.hk
    hA.hpos hA.hP hA.hC hA.hcap hA.hq hA.hEc Kc Kd hA.hKc hA.hKd
  have mem : ∀ (i : Fin FrontAtomStageL.ST) (a : Fin (NW P tf)), (i.val, a) ∈ atL P tf k0 h rT x1T qT eT x2T lT →
      (i.val = 1703 ∧ a = rcT P tf k0 h rT) ∨ (i.val = 1780 ∧ a = x1T) ∨ (i.val = 1781 ∧ a = qcT P tf k0 h qT) ∨
        (i.val = 1782 ∧ a = ecT P tf k0 h eT) ∨ (i.val = 1783 ∧ a = x2T) ∨ (i.val = 1793 ∧ a = lT) := by
    intro i a hm
    simpa only [atL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] using hm
  have nL : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 →
      y ≠ rcT P tf k0 h rT ∧ y ≠ qcT P tf k0 h qT ∧ y ≠ ecT P tf k0 h eT := fun y hy =>
    ⟨fun e => by rw [e, vR] at hy; omega, fun e => by rw [e, vQ] at hy; omega, fun e => by rw [e, vE] at hy; omega⟩
  have nRQ : rcT P tf k0 h rT ≠ qcT P tf k0 h qT := fun e => by have := congrArg Fin.val e; rw [vR, vQ] at this; omega
  have nRE : rcT P tf k0 h rT ≠ ecT P tf k0 h eT := fun e => by have := congrArg Fin.val e; rw [vR, vE] at this; omega
  have nQE : qcT P tf k0 h qT ≠ ecT P tf k0 h eT := fun e => by have := congrArg Fin.val e; rw [vQ, vE] at this; omega
  obtain ⟨st, hinj, hpr⟩ := dockS_step P tf (FrontAtomStageL.stageM m) _ (FrontAtomStageL.sIn r nw q E nf L) Aa Ha hS
    (insL P tf (atL P tf k0 h rT x1T qT eT x2T lT)) (k0 + 12) (ha4 tf k0 h)
    (insL_inj P tf _ (hd_of_nodup P tf _ (by
      simp only [atL, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, not_or, not_false_eq_true]
      exact ⟨⟨(nL x1T l1'.2).1.symm, nRQ, nRE, (nL x2T l2'.2).1.symm, (nL lT ll.2).1.symm⟩,
        ⟨(nL x1T l1'.2).2.1, (nL x1T l1'.2).2.2, h12, h1l⟩, ⟨nQE, (nL x2T l2'.2).2.1.symm, (nL lT ll.2).2.1.symm⟩,
        ⟨(nL x2T l2'.2).2.2.symm, (nL lT ll.2).2.2.symm⟩, h2l⟩)))
    (insL_low P tf _ _ (fun p hp => by
      simp only [atL, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨l1'.1, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨by dsimp only; omega, by dsimp only; omega⟩
      · exact ⟨l2'.1, by dsimp only; omega⟩
      · exact ⟨ll.1, by dsimp only; omega⟩))
    H A3 p3
    (fun i a hi => by
      rw [sIn_eq]
      rcases mem i a (insL_some P tf _ i a hi) with ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ | ⟨e, ha⟩ <;>
        rw [ha]
      · rw [if_pos e]; exact ⟨by rw [m3 _ (by omega), m2 _ (by omega)]; exact w1, (hPr.1 _ (by omega)).2⟩
      · rw [if_neg (by omega), if_pos e]; exact ⟨by rw [L3 _ l1'.2]; exact hx1.1, hx1.2⟩
      · rw [if_neg (by omega), if_neg (by omega), if_pos e]
        exact ⟨by rw [m3 _ (by omega)]; exact w2, (hPr.1 _ (by omega)).2⟩
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]; exact ⟨w3, (hPr.1 _ (by omega)).2⟩
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
        exact ⟨by rw [L3 _ l2'.2]; exact hx2.1, hx2.2⟩
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e]
        exact ⟨by rw [L3 _ ll.2]; exact hl.1, hl.2⟩)
    (fun i hi => by
      have hn := insL_none P tf _ i hi
      have g1 := hn (1703, rcT P tf k0 h rT) (by simp [atL])
      have g2 := hn (1780, x1T) (by simp [atL])
      have g3 := hn (1781, qcT P tf k0 h qT) (by simp [atL])
      have g4 := hn (1782, ecT P tf k0 h eT) (by simp [atL])
      have g5 := hn (1783, x2T) (by simp [atL])
      have g6 := hn (1793, lT) (by simp [atL])
      simp only at g1 g2 g3 g4 g5 g6
      rw [sIn_eq, if_neg (Ne.symm g1), if_neg (Ne.symm g2), if_neg (Ne.symm g3), if_neg (Ne.symm g4),
        if_neg (Ne.symm g5), if_neg (Ne.symm g6)])
  have e4 : k0 + 12 + FrontAtomStageL.ST = k0 + AP := by unfold AP; omega
  rw [e4] at hpr
  refine ⟨_, _, ?_, ?_, ?_, fun y hy n1 n2 n3 => ⟨?_, ?_⟩, hpr⟩
  · unfold atM atCost
    exact Step.seq s1 (Step.seq s2 (Step.seq s3 st))
  · unfold vtT; rw [install_slot _ hinj]; exact hv
  · unfold vtT; rw [dockH_slot _ hinj]; exact hh
  · have hns : ∀ i a, insL P tf (atL P tf k0 h rT x1T qT eT x2T lT) i = some a → a ≠ y := fun i a hi e => by
      rcases mem i a (insL_some P tf _ i a hi) with ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ <;>
        rw [ha] at e
      · exact (nL y hy).1 e.symm
      · exact n1 e.symm
      · exact (nL y hy).2.1 e.symm
      · exact (nL y hy).2.2 e.symm
      · exact n2 e.symm
      · exact n3 e.symm
    rw [install_low P tf _ _ _ _ _ y (by omega) hns, L3 y hy]
  · have hns : ∀ i a, insL P tf (atL P tf k0 h rT x1T qT eT x2T lT) i = some a → a ≠ y := fun i a hi e => by
      rcases mem i a (insL_some P tf _ i a hi) with ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ <;>
        rw [ha] at e
      · exact (nL y hy).1 e.symm
      · exact n1 e.symm
      · exact (nL y hy).2.1 e.symm
      · exact (nL y hy).2.2 e.symm
      · exact n2 e.symm
      · exact n3 e.symm
    rw [dockH_low P tf _ _ _ _ _ y (by omega) hns]

end Phase

end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtP
