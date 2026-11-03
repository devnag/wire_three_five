import Proof.CaseAnalysis.RowsEstimatorReset
import Proof.CaseAnalysis.RowsEstimatorReuseJoin

/-! The original physical estimator, private reset, six-field append and
owned scratch sweep, composed in one finite program. D and every row input
remain physically supplied by the enclosing metadata producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (a : WilliamsAlgorithm):=TapeEmbedding.machine 2 (Reset.machine a)
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) (out : List Bool):=
  Composition.leftConfig 24 (TapeEmbedding.config
    (![out.length,0] : Fin 2→ℕ) (![out,List.replicate D true] : Fin 2→List Bool)
    (Reset.entry a row C D Q q denominator select))

def budget (fuel b D : ℕ):=(2*fuel+2)+1+afterBudget b D

theorem record_private (p : Program) : (Whole.recordSlot p).val≠52 ∧ (Whole.recordSlot p).val≠68:=by
  unfold Whole.recordSlot WholePrefix.slots
  split_ifs <;>simp only [Fin.val_natAdd] <;>omega
theorem record_caps (p : Program) (D : ℕ) : Reset.caps p D (Whole.recordSlot p)=D:=by
  unfold Reset.caps
  exact if_neg (by rcases record_private p with ⟨h1,h2⟩;tauto)

theorem work_old (p : Program) (i : Fin (WholePrefix.tapes p-2)) :
    work p i=old p ⟨(work p i).val,(work_bounds p i).1⟩ := Fin.ext rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
