import Proof.CaseAnalysis.RowsCommonInput
import Proof.Supplier.EquationRowProducer

/-! The raw signed row is physically printed into the matrix request before
the existing count-table and six-field record caller runs. The initial
metadata contains only Q, parity, the selection mask and scalar fields.
The row-printing budget is added once to the complete table budget. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawRecord
open LocalBitMultitape MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open RepairRepresentation
open CompetitorCrossScheduler (producer)
open CompetitorMonomialStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := 130+CompetitorCountTableRecord.tapes p
def receive (p : Program) (i : Fin (CompetitorCountTableRecord.tapes p)) : Fin (tapes p) :=
  if i.val=0 then ⟨128,by unfold tapes; omega⟩ else i.natAdd 130
noncomputable def first (p : Program) :=
  TapeEmbedding.machine (CompetitorCountTableRecord.tapes p) EquationRowFramed.machine
noncomputable def last {s : ℕ} (p : Program) (callee : Machine (CompetitorCountTableRecord.tapes p) s) :=
  RecoveryFocus.machine (receive p) callee
noncomputable def machine {s : ℕ} (p : Program) (callee : Machine (CompetitorCountTableRecord.tapes p) s) :=
  Composition.machine (first p) (last p callee)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ) :=
  EquationRowFramed.uniformBudget row+1+CompetitorCountTableRecord.budget a (EquationRow.request row) Q

theorem receive_injective (p : Program) : Function.Injective (receive p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [receive] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawRecord
