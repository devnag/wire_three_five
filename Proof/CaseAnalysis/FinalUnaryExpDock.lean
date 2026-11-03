import Proof.CaseAnalysis.FinalWordEngines
import Proof.CaseAnalysis.CapacityPower
import Proof.PCP.ProjectionNormalizationDriverAtoms
import Proof.CaseAnalysis.Language
import Proof.CaseAnalysis.ScheduleClauseWidth

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryExpDock

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines
  (dockH_all_zero fixedWord_dock product_dock)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The engine's entry layout -/

/-- `Power.input d` puts the unary exponent on slot `0` and nothing anywhere
else.  Stated once so the dock never unfolds it again. -/
theorem powerInput_other (d : ℕ) (j : Fin 17) (hj : j ≠ 0) :
    RepairSource.CloseoutCapacity.Power.input d j = [] := by
  have hv : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
  simp [RepairSource.CloseoutCapacity.Power.input, hv]

/-! ## §2 The unary exponentiator, docked -/

/-- **The unary exponentiator, docked.**  `List.replicate d true` on `slots 0`
becomes `List.replicate (2 ^ d) true` on `slots 15` and
`UnaryTemplate.tape (2 ^ d)` on `slots 13`, in
`CloseoutCapacity.Power.budget d` steps, every head zero on entry and on exit,
and every tape outside the slot map untouched.  Slots `1`-`12`, `14` and `16`
are the engine's private workspace and must start empty.

This is `PRE.md` §5's "unary exponentiator", and it is a citation of
`CloseoutCapacity.Power.power_run` rather than a new machine. -/
theorem exp_dock {m : ℕ} (d : ℕ) (slots : Fin 17 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate d true)
    (hblank : ∀ j : Fin 17, j ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots RepairSource.CloseoutCapacity.Power.machine)
        (RepairSource.CloseoutCapacity.Power.budget d) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 15) = List.replicate (2 ^ d) true ∧
      A' (slots 13) = UnaryTemplate.tape (2 ^ d) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨out, ⟨rc, hrun, ht, hh, hs⟩, h15, h13⟩ :=
    RepairSource.CloseoutCapacity.Power.power_run d
  have hstep : Step RepairSource.CloseoutCapacity.Power.machine
      (RepairSource.CloseoutCapacity.Power.budget d) (fun _ => 0)
      (RepairSource.CloseoutCapacity.Power.input d) (fun _ => 0) out :=
    ⟨rc, hrun, funext hh, ht, hs⟩
  have hA : ∀ j : Fin 17, A (slots j) = RepairSource.CloseoutCapacity.Power.input d j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simpa [RepairSource.CloseoutCapacity.Power.input] using h0
    · rw [powerInput_other d j hj]
      exact hblank j hj
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A out 15).trans h15
  · exact (install_slot slots hinj A out 13).trans h13
  · intro i hi
    exact install_other slots A out i hi

/-! ## §3 The sentinel-word converter, docked -/

/-- **`List.replicate n true` to `CompareMachine.word n`, docked.**  The unary
input slot is RESTORED, `slots 2` carries the sentinel word the C10 loop reads,
`slots 1` and `slots 3` are the private scratch tapes. -/
theorem counter_dock {m : ℕ} (n : ℕ) (slots : Fin 4 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate n true)
    (h1 : A (slots 1) = [])
    (h2 : A (slots 2) = [])
    (h3 : A (slots 3) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots RepairSource.ProjectionNormalization.Counter.machine)
        (RepairSource.ProjectionNormalization.Counter.budget n) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = List.replicate n true ∧
      A' (slots 2) = CompareMachine.word n ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨out, ⟨rc, hrun, ht, hh, hs⟩, c0, c2⟩ :=
    RepairSource.ProjectionNormalization.DriverAtoms.counter_run n
  have hstep : Step RepairSource.ProjectionNormalization.Counter.machine
      (RepairSource.ProjectionNormalization.Counter.budget n) (fun _ => 0)
      (RepairSource.ProjectionNormalization.Counter.input n) (fun _ => 0) out :=
    ⟨rc, hrun, funext hh, ht, hs⟩
  have hA : ∀ j : Fin 4,
      A (slots j) = RepairSource.ProjectionNormalization.Counter.input n j := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A out 0).trans c0
  · exact (install_slot slots hinj A out 2).trans c2
  · intro i hi
    exact install_other slots A out i hi

/-! ## §4 The exponentiated sentinel word, from one machine -/

/-- The exponentiator's seventeen slots inside the twenty-slot window. -/
def powIdx : Fin 17 → Fin 20 := fun i => i.castAdd 3

/-- The converter's four slots inside the same window: the exponentiator's raw
unary output slot `15` IS the converter's input, so the handoff is not assumed
-- it is the same tape.  Slots `17`, `18`, `19` are fresh. -/
def cntIdx : Fin 4 → Fin 20 := ![15, 17, 18, 19]

theorem powIdx_injective : Function.Injective powIdx := by decide
theorem cntIdx_injective : Function.Injective cntIdx := by decide
theorem powIdx_zero : powIdx 0 = (0 : Fin 20) := by decide
theorem powIdx_thirteen : powIdx 13 = (13 : Fin 20) := by decide
theorem powIdx_fifteen : powIdx 15 = (15 : Fin 20) := by decide
theorem powIdx_ne_zero : ∀ j : Fin 17, j ≠ 0 → powIdx j ≠ (0 : Fin 20) := by decide
theorem powIdx_ne_seventeen : ∀ j : Fin 17, powIdx j ≠ (17 : Fin 20) := by decide
theorem powIdx_ne_eighteen : ∀ j : Fin 17, powIdx j ≠ (18 : Fin 20) := by decide
theorem powIdx_ne_nineteen : ∀ j : Fin 17, powIdx j ≠ (19 : Fin 20) := by decide
theorem cntIdx_zero : cntIdx 0 = (15 : Fin 20) := by decide
theorem cntIdx_one : cntIdx 1 = (17 : Fin 20) := by decide
theorem cntIdx_two : cntIdx 2 = (18 : Fin 20) := by decide
theorem cntIdx_three : cntIdx 3 = (19 : Fin 20) := by decide
theorem cntIdx_ne_thirteen : ∀ j : Fin 4, cntIdx j ≠ (13 : Fin 20) := by decide

/-- **The exponentiating prologue machine**: the corpus's unary exponentiator
followed by the corpus's sentinel-word converter, each focused at its own slots
of one twenty-slot window. -/
noncomputable def expWordMachine {m : ℕ} (slots : Fin 20 → Fin m) :=
  Composition.machine
    (RecoveryFocus.machine (fun j => slots (powIdx j))
      RepairSource.CloseoutCapacity.Power.machine)
    (RecoveryFocus.machine (fun j => slots (cntIdx j))
      RepairSource.ProjectionNormalization.Counter.machine)

/-- **`List.replicate d true` to `CompareMachine.word (2 ^ d)`, on one tape,
from one machine.**  One `Step` of `expWordMachine` takes the unary exponent on
`slots 0` to the exponentiated SENTINEL word on `slots 18` -- the physical form
the C10 clause-address loop reads as its round counter
(`CloseoutRowsOriginalClauseLoop.run`, `Proof/CaseAnalysis/RowsOriginalClauseLoop.lean`)
-- with the raw unary word on `slots 15` and the template form on `slots 13`
available alongside, all heads zero on entry and exit, and every tape outside
the window untouched. -/
theorem expWord_dock {m : ℕ} (d : ℕ) (slots : Fin 20 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = List.replicate d true)
    (hblank : ∀ j : Fin 20, j ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (expWordMachine slots)
        (RepairSource.CloseoutCapacity.Power.budget d + 1 +
          RepairSource.ProjectionNormalization.Counter.budget (2 ^ d)) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 15) = List.replicate (2 ^ d) true ∧
      A' (slots 13) = UnaryTemplate.tape (2 ^ d) ∧
      A' (slots 18) = CompareMachine.word (2 ^ d) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨H₁, A₁, hstep₁, hzero₁, p15, p13, prest⟩ :=
    exp_dock d (fun j => slots (powIdx j)) (hinj.comp powIdx_injective) H A hH
      (by simpa only [powIdx_zero] using h0)
      (fun j hj => hblank (powIdx j) (powIdx_ne_zero j hj))
  have q15 : A₁ (slots 15) = List.replicate (2 ^ d) true := by
    simpa only [powIdx_fifteen] using p15
  have q13 : A₁ (slots 13) = UnaryTemplate.tape (2 ^ d) := by
    simpa only [powIdx_thirteen] using p13
  have q17 : A₁ (slots 17) = [] :=
    (prest (slots 17) (fun j => hinj.ne (powIdx_ne_seventeen j))).trans
      (hblank 17 (by decide))
  have q18 : A₁ (slots 18) = [] :=
    (prest (slots 18) (fun j => hinj.ne (powIdx_ne_eighteen j))).trans
      (hblank 18 (by decide))
  have q19 : A₁ (slots 19) = [] :=
    (prest (slots 19) (fun j => hinj.ne (powIdx_ne_nineteen j))).trans
      (hblank 19 (by decide))
  obtain ⟨H₂, A₂, hstep₂, hzero₂, r0, r2, rrest⟩ :=
    counter_dock (2 ^ d) (fun j => slots (cntIdx j)) (hinj.comp cntIdx_injective) H₁ A₁ hzero₁
      (by simpa only [cntIdx_zero] using q15)
      (by simpa only [cntIdx_one] using q17)
      (by simpa only [cntIdx_two] using q18)
      (by simpa only [cntIdx_three] using q19)
  refine ⟨H₂, A₂, hstep₁.seq hstep₂, hzero₂, ?_, ?_, ?_, ?_⟩
  · simpa only [cntIdx_zero] using r0
  · exact (rrest (slots 13) (fun j => hinj.ne (cntIdx_ne_thirteen j))).trans q13
  · simpa only [cntIdx_two] using r2
  · intro i hi
    exact (rrest i (fun j => hi (cntIdx j))).trans (prest i (fun j => hi (powIdx j)))

/-! ## §5 The paper's envelope `M`, on a tape -/

theorem envelopeCounter_dock {m : ℕ} (clauseDegree q : ℕ) (slots : Fin 20 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) =
      List.replicate (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) true)
    (hblank : ∀ j : Fin 20, j ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (expWordMachine slots)
        (RepairSource.CloseoutCapacity.Power.budget
            (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) + 1 +
          RepairSource.ProjectionNormalization.Counter.budget
            (2 ^ RepairSource.CloseoutLanguage.clauseWidth clauseDegree q)) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 15) =
        List.replicate (2 ^ RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) true ∧
      A' (slots 18) =
        CompareMachine.word (2 ^ RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨H', A', hstep, hzero, g15, _, g18, grest⟩ :=
    expWord_dock (RepairSource.CloseoutLanguage.clauseWidth clauseDegree q) slots hinj H A hH
      h0 hblank
  exact ⟨H', A', hstep, hzero, g15, g18, grest⟩

/-! ## §6 The clause width itself, on a tape -/

/-- **`Nat.clog` on tape, docked.**  `List.replicate q true` on the schedule
program's slot `0` becomes `CompareMachine.word (clauseWidth D q)` on
`slots (Clause.widthSlot D)` -- the paper's
`r(N) = ceil(d_G log_2 (q+2))` (`paper.tex:4513`), computed by an executed
program rather than supplied.  `slots (Clause.qSlot D)` comes back carrying the
incremented `List.replicate (q+1) true`; every other slot of the window is the
program's private workspace and must start empty. -/
theorem clauseWidth_dock {m : ℕ} (D q : ℕ) (hD : 1 ≤ D)
    (slots : Fin (RepairSource.CloseoutSchedule.Clause.tapes D) → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots (RepairSource.CloseoutSchedule.Clause.qSlot D)) = List.replicate q true)
    (hblank : ∀ j : Fin (RepairSource.CloseoutSchedule.Clause.tapes D),
      j.val ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots (RepairSource.CloseoutSchedule.Clause.machine D))
        (RepairSource.CloseoutSchedule.Clause.budget D q) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots (RepairSource.CloseoutSchedule.Clause.qSlot D)) = List.replicate (q + 1) true ∧
      A' (slots (RepairSource.CloseoutSchedule.Clause.widthSlot D)) =
        CompareMachine.word (RepairSource.CloseoutLanguage.clauseWidth D q) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨out, ⟨rc, hrun, ht, hh, hs⟩, hq, hw⟩ :=
    RepairSource.CloseoutSchedule.Clause.clause_run D q hD
  have hstep : Step (RepairSource.CloseoutSchedule.Clause.machine D)
      (RepairSource.CloseoutSchedule.Clause.budget D q) (fun _ => 0)
      (RepairSource.CloseoutSchedule.Clause.input D q) (fun _ => 0) out :=
    ⟨rc, hrun, funext hh, ht, hs⟩
  have hA : ∀ j, A (slots j) = RepairSource.CloseoutSchedule.Clause.input D q j := by
    intro j
    by_cases hj : j.val = 0
    · have hq0 : j = RepairSource.CloseoutSchedule.Clause.qSlot D := Fin.ext (by rw [hj]; rfl)
      rw [hq0]
      simpa [RepairSource.CloseoutSchedule.Clause.input,
        RepairSource.CloseoutSchedule.Clause.qSlot] using h0
    · rw [show RepairSource.CloseoutSchedule.Clause.input D q j = [] by
        simp [RepairSource.CloseoutSchedule.Clause.input, hj]]
      exact hblank j hj
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_⟩
  · exact (install_slot slots hinj A out
      (RepairSource.CloseoutSchedule.Clause.qSlot D)).trans hq
  · exact (install_slot slots hinj A out
      (RepairSource.CloseoutSchedule.Clause.widthSlot D)).trans hw
  · intro i hi
    exact install_other slots A out i hi

/-! ## §7 A sentinel word back to raw unary -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryExpDock
