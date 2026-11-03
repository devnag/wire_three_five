import Proof.MachineModel.Layout
import Proof.Foundations.OrdinaryRewindCarrier
import Proof.Foundations.RepresentationSourceContracts

namespace NearCubicWires.RepairSource.CloseoutFinal.C10WordFunctionDock

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The worker's entry slot, and the entry layout as a slot condition -/

/-- The single tape a `Program`'s run reads its request from.  `Program.twoTapes`
(`Proof/Foundations/OrdinaryMachine.lean`) is what makes `0` a legal index. -/
def inSlot (p : Program) : Fin p.tapeCount := ⟨0, by have h := p.twoTapes; omega⟩

@[simp] theorem inputTapes_inSlot (p : Program) (w : List Bool) :
    p.inputTapes w (inSlot p) = frame w := by
  simp [Program.inputTapes, inSlot]

theorem inputTapes_off (p : Program) (w : List Bool) (j : Fin p.tapeCount)
    (hj : j ≠ inSlot p) : p.inputTapes w j = [] := by
  have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
  simp [Program.inputTapes, hv]

/-- **The entry layout, as a condition on the AMBIENT.**  A caller supplies its
own tape function `A` on `Fin N`; all the worker demands is the framed request
at the image of its entry slot and blanks at the image of its other slots.
Every ambient tape outside `slots`'s image is unconstrained. -/
theorem entry_slots (p : Program) (w : List Bool) {N : ℕ} (slots : Fin p.tapeCount → Fin N)
    (A : Fin N → List Bool) (hin : A (slots (inSlot p)) = frame w)
    (hblank : ∀ j, j ≠ inSlot p → A (slots j) = []) :
    ∀ j, A (slots j) = p.inputTapes w j := by
  intro j
  by_cases hj : j = inSlot p
  · subst hj; rw [hin, inputTapes_inSlot]
  · rw [hblank j hj, inputTapes_off p w j hj]

/-! ## §2 The imported run, as a `Step` on the worker's own tapes -/

/-- The same for a `RewoundWordFunction` (`Proof/Foundations/OrdinaryMachine.lean`),
whose `headsReset` field pins the exit heads at `0`. -/
theorem step_of_rewound {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (wf : RewoundWordFunction Request input output budget)
    (r : Request) :
    ∃ tout : Fin wf.program.tapeCount → List Bool,
      tout wf.program.outputTape = output r ∧
      Step wf.program.machine (budget r) (fun _ => 0)
        (wf.program.inputTapes (input r)) (fun _ => 0) tout := by
  obtain ⟨receipt, hrun, hout⟩ := wf.realizes r
  refine ⟨receipt.final.tapes, hout, Step.of_run hrun ?_ rfl⟩
  funext i
  exact wf.headsReset r receipt hrun i

/-! ## §3 The head bookkeeping of the dock -/

theorem dockH_zero {t u : ℕ} (slots : Fin t → Fin u) :
    dockH slots (fun _ => 0) (fun _ => 0) = (fun _ : Fin u => 0) := by
  funext i
  cases hp : RecoveryFocus.pick slots i <;> simp [dockH, hp]

/-! ## §4 THE ADAPTER -- a `WordFunction` as a `Step` at a caller-chosen layout -/

/-! ## §5 The same with BOTH exit functions explicit -/

/-- **The adapter with the exit heads pinned.**  Same layout freedom as §4, and
now the exit head function is the explicit `dockH slots H (fun _ => 0)`: zero on
the worker's slots, the caller's own `H` everywhere else. -/
theorem rewound_dock {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (wf : RewoundWordFunction Request input output budget) {N : ℕ}
    (slots : Fin wf.program.tapeCount → Fin N) (hinj : Function.Injective slots)
    (H : Fin N → ℕ) (A : Fin N → List Bool) (r : Request)
    (hheads : ∀ j, H (slots j) = 0)
    (hin : A (slots (inSlot wf.program)) = frame (input r))
    (hblank : ∀ j, j ≠ inSlot wf.program → A (slots j) = []) :
    ∃ tout : Fin wf.program.tapeCount → List Bool,
      tout wf.program.outputTape = output r ∧
      Step (RecoveryFocus.machine slots wf.program.machine) (budget r) H A
        (dockH slots H (fun _ => 0)) (install slots A tout) := by
  obtain ⟨tout, houteq, hstep⟩ := step_of_rewound wf r
  exact ⟨tout, houteq,
    hstep.dock slots hinj H A hheads (entry_slots wf.program (input r) slots A hin hblank)⟩

theorem rewound_bank_dock {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (wf : RewoundWordFunction Request input output budget) {N : ℕ}
    (slots : Fin wf.program.tapeCount → Fin N) (hinj : Function.Injective slots)
    (A : Fin N → List Bool) (r : Request)
    (hin : A (slots (inSlot wf.program)) = frame (input r))
    (hblank : ∀ j, j ≠ inSlot wf.program → A (slots j) = []) :
    ∃ tout : Fin wf.program.tapeCount → List Bool,
      tout wf.program.outputTape = output r ∧
      Step (RecoveryFocus.machine slots wf.program.machine) (budget r) (fun _ => 0) A
        (fun _ => 0) (install slots A tout) := by
  obtain ⟨tout, houteq, hstep⟩ :=
    rewound_dock wf slots hinj (fun _ => 0) A r (fun _ => rfl) hin hblank
  refine ⟨tout, houteq, ?_⟩
  rwa [dockH_zero slots] at hstep

/-! ## §6 Every `WordFunction` reaches §5, through the corpus's paid rewind -/

/-- The rewound program of a word function: `Rewind.program`
(`Proof/Foundations/OrdinaryRewindCarrier.lean`), one extra tape and `2 * budget + 2`
fuel, which is what `WordFunction.reset` (`Proof/Foundations/OrdinaryRewindCarrier.lean`)
charges for returning every head to `0`. -/
noncomputable def rewound {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (wf : WordFunction Request input output budget) : Program :=
  Rewind.program wf.program

/-- **The universal form.**  No `RewoundWordFunction` hypothesis: any
`WordFunction` at all docks with both exit functions explicit, paying the
rewind's `2 * budget r + 2`. -/
theorem wordFunction_bank_dock {Request : Type} {input output : Request → List Bool}
    {budget : Request → ℕ} (wf : WordFunction Request input output budget) {N : ℕ}
    (slots : Fin (rewound wf).tapeCount → Fin N) (hinj : Function.Injective slots)
    (A : Fin N → List Bool) (r : Request)
    (hin : A (slots (inSlot (rewound wf))) = frame (input r))
    (hblank : ∀ j, j ≠ inSlot (rewound wf) → A (slots j) = []) :
    ∃ tout : Fin (rewound wf).tapeCount → List Bool,
      tout (rewound wf).outputTape = output r ∧
      Step (RecoveryFocus.machine slots (rewound wf).machine) (2 * budget r + 2)
        (fun _ => 0) A (fun _ => 0) (install slots A tout) :=
  rewound_bank_dock wf.reset slots hinj A r hin hblank

/-! ## §7 The two PCPP query fields, docked

These are the instantiations the C.10.1 decode wants, and they are the type
anchor of this module: their statements name the quantities `paper.tex` names
for the invoked algorithm -- the indexed clause's two literals with their signs
(`paper.tex:4132-4133`) and the systematic coordinate's support
(`paper.tex:3912-3913`) -- at the source contract's polynomial budget.

They are pure instantiations of §6: no new machine, no new hypothesis, and in
particular **no claim that the request word is already on the bank**.  Putting
`frame (pcppInput rq ++ natWord i.val)` where `hin` wants it is a separate
loader and is NOT done here. -/

/-- **The clause decode, docked.**  `PCPPQueryRealization.clause`
(`Proof/Foundations/RepresentationSourceContracts.lean`) outputs exactly the pair of
literal indices that `sitePolynomial` (`Proof/CaseAnalysis/FinalExactness.lean`)
reads a clause address through. -/
theorem clause_dock (a : PointwisePCPPAlgorithm) (Q : PCPPQueryRealization a) {N : ℕ}
    (slots : Fin (rewound Q.clause).tapeCount → Fin N) (hinj : Function.Injective slots)
    (A : Fin N → List Bool) (rq : PCPPRequest a.minimumArity)
    (i : Fin (2 ^ (a.output rq).clauseBits))
    (hin : A (slots (inSlot (rewound Q.clause))) =
      frame (pcppInput rq ++ natWord i.val))
    (hblank : ∀ j, j ≠ inSlot (rewound Q.clause) → A (slots j) = []) :
    ∃ tout : Fin (rewound Q.clause).tapeCount → List Bool,
      tout (rewound Q.clause).outputTape =
        natListWord [literalIndex ((a.output rq).clauses i).left,
          literalIndex ((a.output rq).clauses i).right] ∧
      Step (RecoveryFocus.machine slots (rewound Q.clause).machine)
        (2 * (Q.coefficient * (rq.circuit.size + rq.arity + 1) ^ Q.degree) + 2)
        (fun _ => 0) A (fun _ => 0) (install slots A tout) :=
  wordFunction_bank_dock Q.clause slots hinj A ⟨rq, i⟩ hin hblank

end NearCubicWires.RepairSource.CloseoutFinal.C10WordFunctionDock
