import Proof.Wire_3_5.UnionMachine.FrontEntries
import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # C6 front, U1b: the grid sums' validator as a stage (P3:3669-3671)

Docks the entries validator (`FrontEntries.entP_spec`) as one machine on its own `22` tapes, from the framed input
`x` (tape `0`, only counted), the framed rest of the guess `r` (tape `1`) and the entry count `1^E` (tape `2`): base's
metadata counter (`1^{|x|}`), the register fill (`FrontFill`), the cell, the validator. Its cell (tape `11`) is
`(entScan E r).isSome`: `E` grid entries of the codec (grid sign, canonical atom code), then zero padding.
Main statement: **`entries_ready`**. Paper quantity: the validity of the guess's grid sums. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef
open NearCubicWires.RepairSource.CloseoutSchedule

/-! ## Layout: `0` input, `1` rest, `2` count; `3–9` counter scratch; `10` fill marker; `11` cell; `12–21` registers -/

abbrev ET : ℕ := 22

def mtS (j : Fin 8) : Fin ET := ⟨if j.val = 0 then 0 else 2 + j.val, by have := j.isLt; simp only [ET]; split <;> omega⟩
def eS (j : Fin 13) : Fin ET := ⟨if j.val = 0 then 1 else if j.val = 1 then 11 else if j.val = 2 then 2 else 9 + j.val,
  by have := j.isLt; simp only [ET]; split_ifs <;> omega⟩

theorem mtS_inj : Function.Injective mtS := by
  intro a b h; have := congrArg Fin.val h; simp only [mtS] at this; apply Fin.ext; split_ifs at this <;> omega
theorem eS_inj : Function.Injective eS := by
  intro a b h; have := congrArg Fin.val h; simp only [eS] at this; apply Fin.ext; split_ifs at this <;> omega

theorem mtS_ne (i : Fin ET) (hi : i.val = 1 ∨ i.val = 2 ∨ 10 ≤ i.val) : ∀ j, mtS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; simp only [mtS] at e; split_ifs at e <;> omega
theorem eS_ne (i : Fin ET) (hi : i.val = 0 ∨ (3 ≤ i.val ∧ i.val ≤ 10)) : ∀ j, eS j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; simp only [eS] at e; split_ifs at e <;> omega

def tgtE (i : Fin ET) : Bool := decide (12 ≤ i.val)

noncomputable def countM := Composition.machine Metadata.lengthProgram Metadata.copyProgram

/-- **The entries stage.** -/
noncomputable def esMachine :=
  Composition.machine (RecoveryFocus.machine mtS countM)
  (Composition.machine (FrontFill.fillP (4 : Fin ET) 10 tgtE).compile
  (Composition.machine (cellP (11 : Fin ET)).compile
    (RecoveryFocus.machine eS FrontEntries.entP.toProg.compile)))

def esIn (x r : List Bool) (E : ℕ) : Fin ET → List Bool := fun i =>
  if i.val = 0 then frame x else if i.val = 1 then frame r else if i.val = 2 then List.replicate E true else []

noncomputable def esCost (x r : List Bool) : ℕ :=
  (4 * x.length + 5 + 1 + (2 * x.length + 6)) + 1 + ((11 * x.length + 20) + 1 + (1 + 1 +
    FrontEntries.entCost r.length))

/-- **The entries stage**: its cell (tape `11`) is `(entScan E r).isSome`; the input, the rest and the count kept. -/
theorem entries_ready (x r : List Bool) (E : ℕ) (hx : r.length + 1 ≤ x.length) :
    ∃ out : Fin ET → List Bool, ClockJoin.ReadyRun esMachine (esCost x r) (esIn x r E) out ∧
      out 11 = [(entScan E r).isSome] ∧ out 0 = frame x ∧ out 1 = frame r ∧ out 2 = List.replicate E true := by
  -- 1. `1^{|x|}`
  have g1r : ClockJoin.ReadyRun countM (4 * x.length + 5 + 1 + (2 * x.length + 6)) (Metadata.input x)
      (Metadata.copied x) :=
    ClockJoin.join _ _ _ _ _ _ _ (Metadata.length_run x) (Metadata.copy_run x)
  have g1 := g1r.focus mtS mtS_inj (esIn x r E) (by
    intro j; fin_cases j <;> simp [esIn, mtS, Metadata.input, ET])
  set a1 := install mtS (esIn x r E) (Metadata.copied x) with ha1
  have a1_hi : ∀ i : Fin ET, 10 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (mtS_ne i (by omega))]
    unfold esIn; split_ifs <;> first | rfl | omega
  have a1_1 : a1 1 = frame r := by rw [ha1, install_other _ _ _ _ (mtS_ne 1 (by decide))]; simp [esIn, ET]
  have a1_2 : a1 2 = List.replicate E true := by
    rw [ha1, install_other _ _ _ _ (mtS_ne 2 (by decide))]; simp [esIn, ET]
  have a1_0 : a1 0 = frame x := by rw [ha1, show (0 : Fin ET) = mtS 0 from rfl, install_slot _ mtS_inj]; rfl
  have a1_4 : a1 4 = List.replicate x.length true := by
    rw [ha1, show (4 : Fin ET) = mtS 2 from rfl, install_slot _ mtS_inj]; rfl
  -- 2. the registers
  have hside : ∀ i, FrontFill.side 10 tgtE i → 10 ≤ i.val := by
    intro i hi; rcases hi with h | h
    · simp [tgtE] at h; omega
    · rw [h]; decide
  have g2 := fill_ready (4 : Fin ET) 10 tgtE a1 x.length (by decide) (by decide) (by decide) a1_4
    (fun i hi => a1_hi i (hside i hi))
  set a2 := (fun i => if FrontFill.side 10 tgtE i then List.replicate (2 * x.length + 3) false else a1 i) with ha2
  have a2_other : ∀ i : Fin ET, (i.val < 10 ∨ i.val = 11) → a2 i = a1 i := by
    intro i hi
    rw [ha2]; simp only
    rw [if_neg]
    rintro (h | h)
    · simp [tgtE] at h; omega
    · rw [h] at hi; simp [ET] at hi
  -- 3. the cell
  have g3 := cell_ready (11 : Fin ET) a2 (by rw [a2_other _ (by decide)]; exact a1_hi _ (by decide))
  set a3 := Function.update a2 (11 : Fin ET) [false] with ha3
  -- 4. the validator
  set cap := 2 * x.length + 2 with hcap
  obtain ⟨n, hn, hent⟩ := FrontEntries.entP_spec cap r E false (by omega)
  have g4r := wm_ready _ cap _ _ _ hent (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
  have g4 := g4r.focus eS eS_inj a3 (by
    intro j
    fin_cases j
    · show a3 1 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_1]; rfl
    · show a3 11 = _
      rw [ha3, Function.update_self]; rfl
    · show a3 2 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_2]; rfl
    all_goals
      (rw [ha3, Function.update_of_ne (by decide)]
       simp [ha2, FrontFill.side, tgtE, eS, wenc, role, FrontEntries.st, FrontEntries.d0, regTape_zero, hcap]))
  set a4 := install eS a3 (wenc cap (FrontEntries.st r E (FrontEntries.dF (entScan E r).isSome))).A with ha4
  refine ⟨a4, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 g4))) (by simp only [esCost]; omega), ?_, ?_, ?_, ?_⟩
  · rw [ha4, show (11 : Fin ET) = eS 1 from rfl, install_slot _ eS_inj]
    simp [wenc, role, FrontEntries.st, FrontEntries.dF]
  · rw [ha4, install_other _ _ _ _ (eS_ne 0 (by decide)), ha3, Function.update_of_ne (by decide),
      a2_other _ (by decide), a1_0]
  · rw [ha4, show (1 : Fin ET) = eS 0 from rfl, install_slot _ eS_inj]
    simp [wenc, role, FrontEntries.st]
  · rw [ha4, show (2 : Fin ET) = eS 2 from rfl, install_slot _ eS_inj]
    simp [wenc, role, FrontEntries.st]

end NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesStage
