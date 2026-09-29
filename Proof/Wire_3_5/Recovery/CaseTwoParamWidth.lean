import Proof.Wire_3_5.Recovery.CaseTwoFold

/-! # The Case-2 widths of the selected slice (P3:3637-3640, 3665-3667; D1.6 A3b)

Realizes, for the hybrid Case-2 machine, the widths of the padded Case-2 table at the selected source length
`N = 2^S`: the padded width `q(N) = ⌈log₂T(N)⌉ + A_pad⌈log₂(log₂T(N)+2)⌉ + A_pad` (P3:3637-3640; `widthMachine`,
`q(2^S) = widthAt k A S`) and the occurrence address width `q + ⌈d_G log₂(q+2)⌉ + 1` (P3:3665-3667, `q_0` of
`tr:address-width`; base's `Clause` machine for `⌈D log₂(q+2)⌉`, base's unary sum). Both are unary words: the fold's
width port `1^q` and its block width `1^w`.

Paper quantity of the main type (`paramWidth_run`): from `1^S`, `1^{q(2^S)}` and `1^{q(2^S) + 1 + ⌈D log₂(q+2)⌉}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Width
variable (k A D : ℕ)

/-- The clause machine's tape count. -/
abbrev ct : ℕ := Clause.tapes D

/-- The widths' tapes: the width machine (28), base's clause machine, then five: the copy's log, `1^{cw}`, the walk's
log, the sum `1^w`, the sum's log. -/
abbrev pw : ℕ := 28 + ct D + 5

/-- A position of the widths' bank. -/
def wp (m : ℕ) (h : m < pw D) : Fin (pw D) := ⟨m, h⟩

def wslot (i : Fin 28) : Fin (pw D) := ⟨i.val, by have := i.isLt; unfold pw; omega⟩
def cslot (i : Fin (ct D)) : Fin (pw D) := ⟨28 + i.val, by have := i.isLt; unfold pw; omega⟩
def copySlots : Fin 3 → Fin (pw D) :=
  ![wp D 26 (by show _ < 28 + ct D + 5; omega), wp D 28 (by show _ < 28 + ct D + 5; omega), wp D (28 + ct D) (by show _ < 28 + ct D + 5; omega)]
def uwSlots : Fin 3 → Fin (pw D) :=
  ![cslot D (RepairSource.CloseoutSchedule.Clause.widthSlot D), wp D (28 + ct D + 1) (by show _ < 28 + ct D + 5; omega),
    wp D (28 + ct D + 2) (by show _ < 28 + ct D + 5; omega)]
def sumSlots : Fin 4 → Fin (pw D) :=
  ![wp D 28 (by show _ < 28 + ct D + 5; omega), wp D (28 + ct D + 1) (by show _ < 28 + ct D + 5; omega),
    wp D (28 + ct D + 3) (by show _ < 28 + ct D + 5; omega), wp D (28 + ct D + 4) (by show _ < 28 + ct D + 5; omega)]

/-- Close a position goal of the widths' bank by values. -/
macro "pw_tac" : tactic => `(tactic| (first | omega | (simp only [NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamWidth.wp,
  NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamWidth.cslot, NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamWidth.wslot,
  Fin.val_mk] <;> omega)))

theorem widthSlot_val : (RepairSource.CloseoutSchedule.Clause.widthSlot D).val = 24 + 2 * D := by
  simp [RepairSource.CloseoutSchedule.Clause.widthSlot, RepairSource.CloseoutSchedule.Clause.clogSlots]; omega

theorem ct_eq : ct D = 26 + 2 * D := rfl

theorem wslot_inj : Function.Injective (wslot D) := by
  intro a b h; exact Fin.ext (by simpa [wslot] using congrArg Fin.val h)
theorem cslot_inj : Function.Injective (cslot D) := by
  intro a b h; exact Fin.ext (by have := congrArg Fin.val h; simp only [cslot] at this; omega)

theorem copySlots_val (i : Fin 3) : (copySlots D i).val = ![26, 28, 28 + ct D] i := by fin_cases i <;> rfl
theorem uwSlots_val (i : Fin 3) : (uwSlots D i).val = ![28 + (24 + 2 * D), 28 + ct D + 1, 28 + ct D + 2] i := by
  fin_cases i
  · show 28 + (RepairSource.CloseoutSchedule.Clause.widthSlot D).val = _; rw [widthSlot_val]; rfl
  · rfl
  · rfl
theorem sumSlots_val (i : Fin 4) : (sumSlots D i).val = ![28, 28 + ct D + 1, 28 + ct D + 3, 28 + ct D + 4] i := by
  fin_cases i <;> rfl

theorem copySlots_inj : Function.Injective (copySlots D) := by
  intro a b h; have hv := congrArg Fin.val h; rw [copySlots_val, copySlots_val] at hv
  have := ct_eq D; apply Fin.ext; revert hv; fin_cases a <;> fin_cases b <;> simp <;> omega
theorem uwSlots_inj : Function.Injective (uwSlots D) := by
  intro a b h; have hv := congrArg Fin.val h; rw [uwSlots_val, uwSlots_val] at hv
  have := ct_eq D; apply Fin.ext; revert hv; fin_cases a <;> fin_cases b <;> simp <;> omega
theorem sumSlots_inj : Function.Injective (sumSlots D) := by
  intro a b h; have hv := congrArg Fin.val h; rw [sumSlots_val, sumSlots_val] at hv
  have := ct_eq D; apply Fin.ext; revert hv; fin_cases a <;> fin_cases b <;> simp <;> omega

/-- **The widths**: the width machine, a copy of `1^q`, base's clause machine on the copy, the clause width in unary,
and the sum `(q+1) + cw`. -/
noncomputable def paramWidth :=
  Composition.machine (RecoveryFocus.machine (wslot D) (widthMachine k A))
  (Composition.machine (RecoveryFocus.machine (copySlots D) PCPUnaryCopy.machine)
  (Composition.machine (RecoveryFocus.machine (cslot D) (RepairSource.CloseoutSchedule.Clause.machine D))
  (Composition.machine (RecoveryFocus.machine (uwSlots D) (UWalkUnary.machine false false))
    (RecoveryFocus.machine (sumSlots D) ClockUnarySum.machine))))

/-- The widths' input: `1^S` on tape 0. -/
def pwInput (S : ℕ) : Fin (pw D) → List Bool := fun i => if i.val = 0 then List.replicate S true else []

/-- The widths' cost bound. -/
def pwCost (S : ℕ) : ℕ :=
  candWidthBound k A S + 1 + ((2 * widthAt k A S + 4) + 1 +
    (RepairSource.CloseoutSchedule.Clause.budget D (widthAt k A S) + 1 +
      ((2 * RepairSource.CloseoutLanguage.clauseWidth D (widthAt k A S) + 6) + 1 +
        (2 * (widthAt k A S + 1 + RepairSource.CloseoutLanguage.clauseWidth D (widthAt k A S)) + 6))))

/-- **The widths are ready**: from `1^S` they leave `1^S`, `1^{q}` (`q = q(2^S)`) and `1^{q + 1 + cw}`
(`cw = ⌈D log₂(q+2)⌉`). -/
theorem paramWidth_run (S : ℕ) (hD : 1 ≤ D) : ∃ out : Fin (pw D) → List Bool,
    ClockJoin.ReadyRun (paramWidth k A D) (pwCost k A D S) (pwInput D S) out ∧
    out (wp D 0 (by show _ < 28 + ct D + 5; omega)) = List.replicate S true ∧
    out (wp D 26 (by show _ < 28 + ct D + 5; omega)) = List.replicate (widthAt k A S) true ∧
    out (wp D (28 + ct D + 3) (by show _ < 28 + ct D + 5; omega)) =
      List.replicate (widthAt k A S + 1 + RepairSource.CloseoutLanguage.clauseWidth D (widthAt k A S)) true := by
  set q := widthAt k A S with hq
  set cw := RepairSource.CloseoutLanguage.clauseWidth D q with hcw
  have hct := ct_eq D
  have hct' : Clause.tapes D = 26 + 2 * D := hct
  set x := pwInput D S with hx
  -- the width
  obtain ⟨c1, o1, hc1, r1, o10, o126⟩ := widthMachine_run k A S
  have g1 := r1.focus (wslot D) (wslot_inj D) x (by
    intro i
    simp only [hx, pwInput, wslot, widthInput])
  set a1 := install (wslot D) x o1 with ha1
  have a1_hi : ∀ i : Fin (pw D), 28 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [wslot] at this; omega)]
    simp only [hx, pwInput]; rw [if_neg (by omega)]
  have a1_26 : a1 (wp D 26 (by show _ < 28 + ct D + 5; omega)) = List.replicate q true := by
    rw [show wp D 26 _ = wslot D 26 from rfl, ha1, install_slot _ (wslot_inj D), o126]
  have a1_0 : a1 (wp D 0 (by show _ < 28 + ct D + 5; omega)) = List.replicate S true := by
    rw [show wp D 0 _ = wslot D 0 from rfl, ha1, install_slot _ (wslot_inj D), o10]
  -- the copy of `1^q`
  have g2 := (ready_of_root (PCPUnaryCopy.copy_ready q 0 0 0)).focus (copySlots D) (copySlots_inj D) a1 (by
    intro j; fin_cases j
    · show a1 (wp D 26 _) = _; rw [a1_26]; simp
    · show a1 (wp D 28 _) = _; rw [a1_hi _ (by pw_tac)]; rfl
    · show a1 (wp D (28 + ct D) _) = _; rw [a1_hi _ (by pw_tac)]; rfl)
  set a2 := install (copySlots D) a1 ![ZeroPadding.pad 0 (List.replicate q true),
    ZeroPadding.pad 0 (List.replicate q true), List.replicate (max 0 (q + 1)) false] with ha2
  have a2_off : ∀ i : Fin (pw D), i.val ≠ 26 → i.val ≠ 28 → i.val ≠ 28 + ct D → a2 i = a1 i := by
    intro i h1 h2 h3
    rw [ha2, install_other _ _ _ _ (by
      intro j h; have hv := congrArg Fin.val h; rw [copySlots_val] at hv; revert hv
      fin_cases j <;> simp <;> omega)]
  have a2_28 : a2 (wp D 28 (by show _ < 28 + ct D + 5; omega)) = List.replicate q true := by
    rw [show wp D 28 _ = copySlots D 1 from rfl, ha2, install_slot _ (copySlots_inj D)]; simp
  have a2_26 : a2 (wp D 26 (by show _ < 28 + ct D + 5; omega)) = List.replicate q true := by
    rw [show wp D 26 _ = copySlots D 0 from rfl, ha2, install_slot _ (copySlots_inj D)]; simp
  -- the clause width
  obtain ⟨o3, r3, o3q, o3w⟩ := RepairSource.CloseoutSchedule.Clause.clause_run D q hD
  have g3 := r3.focus (cslot D) (cslot_inj D) a2 (by
    intro i
    by_cases h0 : i.val = 0
    · have : i = RepairSource.CloseoutSchedule.Clause.qSlot D := Fin.ext h0
      subst this
      rw [show cslot D (RepairSource.CloseoutSchedule.Clause.qSlot D) = wp D 28 (by show _ < 28 + ct D + 5; omega) from rfl,
        a2_28]
      simp [RepairSource.CloseoutSchedule.Clause.input, RepairSource.CloseoutSchedule.Clause.qSlot]
    · have hi := i.isLt
      rw [a2_off _ (by pw_tac) (by pw_tac) (by pw_tac),
        a1_hi _ (by pw_tac)]
      simp [RepairSource.CloseoutSchedule.Clause.input, h0])
  set a3 := install (cslot D) a2 o3 with ha3
  have a3_off : ∀ i : Fin (pw D), (i.val < 28 ∨ 28 + ct D ≤ i.val) → a3 i = a2 i := by
    intro i hi
    rw [ha3, install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; have := j.isLt; simp [cslot] at *; omega)]
  have a3_w : a3 (cslot D (RepairSource.CloseoutSchedule.Clause.widthSlot D)) = CompareMachine.word cw := by
    rw [ha3, install_slot _ (cslot_inj D), o3w]
  have a3_q : a3 (wp D 28 (by show _ < 28 + ct D + 5; omega)) = List.replicate (q + 1) true := by
    rw [show wp D 28 _ = cslot D (RepairSource.CloseoutSchedule.Clause.qSlot D) from rfl, ha3,
      install_slot _ (cslot_inj D), o3q]
  -- the clause width in unary
  have g4 := (UWalkUnary.ready false false 0 cw).focus (uwSlots D) (uwSlots_inj D) a3 (by
    intro j; fin_cases j
    · show a3 (cslot D (RepairSource.CloseoutSchedule.Clause.widthSlot D)) = _
      rw [a3_w]; simp [UWalkUnary.input, UWalkUnary.source]
    · show a3 (wp D (28 + ct D + 1) _) = _
      rw [a3_off _ (Or.inr (by pw_tac)), a2_off _ (by pw_tac) (by pw_tac) (by pw_tac),
        a1_hi _ (by pw_tac)]; rfl
    · show a3 (wp D (28 + ct D + 2) _) = _
      rw [a3_off _ (Or.inr (by pw_tac)), a2_off _ (by pw_tac) (by pw_tac) (by pw_tac),
        a1_hi _ (by pw_tac)]; rfl)
  set a4 := install (uwSlots D) a3 (UWalkUnary.result false false 0 cw) with ha4
  have a4_off : ∀ i : Fin (pw D), i.val ≠ 28 + (24 + 2 * D) → i.val ≠ 28 + ct D + 1 → i.val ≠ 28 + ct D + 2 →
      a4 i = a3 i := by
    intro i h1 h2 h3
    rw [ha4, install_other _ _ _ _ (by
      intro j h; have hv := congrArg Fin.val h; rw [uwSlots_val] at hv; revert hv
      fin_cases j <;> simp <;> omega)]
  have a4_u : a4 (wp D (28 + ct D + 1) (by show _ < 28 + ct D + 5; omega)) = List.replicate cw true := by
    rw [show wp D (28 + ct D + 1) _ = uwSlots D 1 from rfl, ha4, install_slot _ (uwSlots_inj D)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  -- the sum `(q+1) + cw`
  have g5 := (ClockUnarySum.sum_ready (q + 1) cw).focus (sumSlots D) (sumSlots_inj D) a4 (by
    intro j; fin_cases j
    · exact (a4_off (wp D (28) (by show _ < 28 + ct D + 5; omega)) (by pw_tac) (by pw_tac) (by pw_tac)).trans a3_q
    · exact a4_u
    · exact (a4_off (wp D (28 + ct D + 3) (by show _ < 28 + ct D + 5; omega)) (by pw_tac) (by pw_tac) (by pw_tac)).trans
        ((a3_off (wp D (28 + ct D + 3) (by show _ < 28 + ct D + 5; omega)) (Or.inr (by pw_tac))).trans
        ((a2_off (wp D (28 + ct D + 3) (by show _ < 28 + ct D + 5; omega)) (by pw_tac) (by pw_tac) (by pw_tac)).trans
          (a1_hi (wp D (28 + ct D + 3) (by show _ < 28 + ct D + 5; omega)) (by pw_tac))))
    · exact (a4_off (wp D (28 + ct D + 4) (by show _ < 28 + ct D + 5; omega)) (by pw_tac) (by pw_tac) (by pw_tac)).trans
        ((a3_off (wp D (28 + ct D + 4) (by show _ < 28 + ct D + 5; omega)) (Or.inr (by pw_tac))).trans
        ((a2_off (wp D (28 + ct D + 4) (by show _ < 28 + ct D + 5; omega)) (by pw_tac) (by pw_tac) (by pw_tac)).trans
          (a1_hi (wp D (28 + ct D + 4) (by show _ < 28 + ct D + 5; omega)) (by pw_tac)))))
  set a5 := install (sumSlots D) a4 ![List.replicate (q + 1) true, List.replicate cw true,
    List.replicate (q + 1 + cw) true, List.replicate (q + 1 + cw + 2) false] with ha5
  have a5_off : ∀ i : Fin (pw D), i.val ≠ 28 → i.val ≠ 28 + ct D + 1 → i.val ≠ 28 + ct D + 3 →
      i.val ≠ 28 + ct D + 4 → a5 i = a4 i := by
    intro i h1 h2 h3 h4
    rw [ha5, install_other _ _ _ _ (by
      intro j h; have hv := congrArg Fin.val h; rw [sumSlots_val] at hv; revert hv
      fin_cases j <;> simp <;> omega)]
  refine ⟨a5, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2
    (ClockJoin.join _ _ _ _ _ _ _ g3 (ClockJoin.join _ _ _ _ _ _ _ g4 g5)))) ?_, ?_, ?_, ?_⟩
  · unfold pwCost; rw [← hq]; omega
  · rw [a5_off _ (by pw_tac) (by pw_tac) (by pw_tac) (by pw_tac),
      a4_off _ (by pw_tac) (by pw_tac) (by pw_tac), a3_off _ (Or.inl (by pw_tac)),
      a2_off _ (by pw_tac) (by pw_tac) (by pw_tac), a1_0]
  · rw [a5_off _ (by pw_tac) (by pw_tac) (by pw_tac) (by pw_tac),
      a4_off _ (by pw_tac) (by pw_tac) (by pw_tac), a3_off _ (Or.inl (by pw_tac)), a2_26]
  · rw [show wp D (28 + ct D + 3) _ = sumSlots D 2 from rfl, ha5, install_slot _ (sumSlots_inj D)]; rfl

end Width

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoParamWidth
