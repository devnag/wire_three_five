import Proof.Wire_3_5.UnionMachine.FrontOracle

/-!
# The walker of the guess word, kept: the tag, the pair field's payload, the rest

Paper v2, §H.5: "The weak machine guesses the two circuits `Γ_src` and `Γ_pf` above, a class tag, and one sparse grid
sum for each distinct PCPP variable. It rejects malformed descriptions". The guess word starts with the class tag and
the pair field (`Front35.pairWord`); this stage reads the framed witness once (base's counter `1^{|w|}`, the register
fill, the walker `FrontOracleField.walkP`) and leaves, at zero heads: the tag, the walker's verdict on the field, the
field's payload `frame (payload w.tail)` — the raw pair field the cold front end decodes — and the rest of the guess
`frame (restOf w.tail)`. It is the first four stages of the old oracle stage (`FrontOracle.osMachine`), without the
one-circuit decoder that overwrote the payload tape.

Main statement: **`walk_ready`**. Paper quantity: the guess's tag, its pair field and the rest of the guess.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Front35.Walk

open _root_.NearCubicWires _root_.NearCubicWires.LocalBitMultitape _root_.NearCubicWires.RepairOrdinary
open _root_.NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open _root_.NearCubicWires.WireExponent3_5.FinalPass _root_.NearCubicWires.WireExponent3_5.FinalPass.Tm
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontKit
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontOracle
open _root_.NearCubicWires.RepairSource.CloseoutSchedule _root_.NearCubicWires.WireExponent3_5.UnionMachine

/-- **The walk stage** on the oracle stage's layout (`FrontOracle.OS` tapes; `1` the witness, `11` the walker's cell,
`12` the payload, `13` the rest, `14` the tag). -/
noncomputable def wkMachine :=
  Composition.machine (RecoveryFocus.machine mtS countM)
  (Composition.machine (FrontFill.fillP (4 : Fin OS) 10 tgtW).compile
  (Composition.machine (cellP (11 : Fin OS)).compile
    (RecoveryFocus.machine wS FrontOracleField.walkP.toProg.compile)))

/-- The stage's input: `frame w` on tape `1`, every other tape blank. -/
def wkIn (w : List Bool) : Fin OS → List Bool := fun i => if i.val = 1 then frame w else []

/-- The stage's cost. -/
noncomputable def wkCost (w : List Bool) : ℕ :=
  (4 * w.length + 5 + 1 + (2 * w.length + 6)) + 1 + ((11 * w.length + 20) + 1 + (1 + 1 +
    FrontOracleField.walkCost w.length))

/-- **The walk stage**: the tag on `14`, the rest on `13`, the payload on `12`, the verdict in the cell `11`, the
witness kept on `1`. -/
theorem walk_ready (w : List Bool) :
    ∃ out : Fin OS → List Bool, ClockJoin.ReadyRun wkMachine (wkCost w) (wkIn w) out ∧
      out 14 = [w.headD false] ∧ out 13 = frame (restOf w.tail) ∧ out 12 = frame (payload w.tail) ∧
      out 11 = [FrontOracleField.okOf w] ∧ out 1 = frame w := by
  -- 1. `1^{|w|}`
  have g1r : ClockJoin.ReadyRun countM (4 * w.length + 5 + 1 + (2 * w.length + 6)) (Metadata.input w)
      (Metadata.copied w) :=
    ClockJoin.join _ _ _ _ _ _ _ (Metadata.length_run w) (Metadata.copy_run w)
  have g1 := g1r.focus mtS mtS_inj (wkIn w) (by
    intro j; fin_cases j <;> simp [wkIn, mtS, Metadata.input, OS])
  set a1 := install mtS (wkIn w) (Metadata.copied w) with ha1
  have a1_hi : ∀ i : Fin OS, 10 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (mtS_ne i (by omega))]
    unfold wkIn; split_ifs <;> first | rfl | omega
  have a1_1 : a1 1 = frame w := by
    rw [ha1, show (1 : Fin OS) = mtS 0 from rfl, install_slot _ mtS_inj]; rfl
  have a1_4 : a1 4 = List.replicate w.length true := by
    rw [ha1, show (4 : Fin OS) = mtS 2 from rfl, install_slot _ mtS_inj]; rfl
  -- 2. the walker's registers
  have hsideW : ∀ i, FrontFill.side 10 tgtW i → 10 ≤ i.val := by
    intro i hi; rcases hi with h | h
    · simp [tgtW] at h; omega
    · rw [h]; decide
  have g2 := fill_ready (4 : Fin OS) 10 tgtW a1 w.length (by decide) (by decide) (by decide) a1_4
    (fun i hi => a1_hi i (hsideW i hi))
  set a2 := (fun i => if FrontFill.side 10 tgtW i then List.replicate (2 * w.length + 3) false else a1 i) with ha2
  have a2_other : ∀ i : Fin OS, (i.val < 10 ∨ 25 ≤ i.val ∨ (10 < i.val ∧ i.val < 15)) → a2 i = a1 i := by
    intro i hi
    rw [ha2]; simp only
    rw [if_neg]
    rintro (h | h)
    · simp [tgtW] at h; omega
    · rw [h] at hi; simp [OS] at hi
  -- 3. the walker's cell
  have g3 := cell_ready (11 : Fin OS) a2 (by rw [a2_other _ (by decide)]; exact a1_hi _ (by decide))
  set a3 := Function.update a2 (11 : Fin OS) [false] with ha3
  -- 4. the walker
  set cap := 2 * w.length + 2 with hcap
  have hwk := FrontOracleField.walkP_spec cap w false le_rfl
  have g4r := wm_ready _ cap _ _ _ hwk (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
    (by intro i; fin_cases i <;> rfl) (by intro r; fin_cases r <;> rfl)
  have g4 := g4r.focus wS wS_inj a3 (by
    intro j
    fin_cases j
    · show a3 1 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_1]; rfl
    · show a3 11 = _
      rw [ha3, Function.update_self]; rfl
    · show a3 12 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_hi _ (by decide)]; rfl
    · show a3 13 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_hi _ (by decide)]; rfl
    · show a3 14 = _
      rw [ha3, Function.update_of_ne (by decide), a2_other _ (by decide), a1_hi _ (by decide)]; rfl
    all_goals
      (rw [ha3, Function.update_of_ne (by decide)]
       simp [ha2, FrontFill.side, tgtW, wS, wenc, role, FrontOracleField.st, FrontOracleField.d0, regTape_zero,
         hcap]))
  set a4 := install wS a3 (wenc cap (FrontOracleField.st w (FrontOracleField.dF w))).A with ha4
  have a4_out : ∀ j, a4 (wS j) = (wenc cap (FrontOracleField.st w (FrontOracleField.dF w))).A j :=
    fun j => install_slot _ wS_inj _ _ j
  refine ⟨a4, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 g4))) (by simp [wkCost]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (14 : Fin OS) = wS 4 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [show (13 : Fin OS) = wS 3 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [show (12 : Fin OS) = wS 2 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [show (11 : Fin OS) = wS 1 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st, FrontOracleField.dF]
  · rw [show (1 : Fin OS) = wS 0 from rfl, a4_out]
    simp [wenc, role, FrontOracleField.st]

end NearCubicWires.WireExponent3_5.UnionMachine.Front35.Walk
