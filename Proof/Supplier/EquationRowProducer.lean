import Proof.Supplier.EquationRowFramed
import Proof.Supplier.EquationRowBounds

/-! The composable ordinary row-to-matrix supplier with a uniform proved
budget and physical reset. No local execution record is an input premise. -/
namespace NearCubicWires.RepairOrdinary.EquationRowFramed
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def uniformBudget (r : EquationRow.Input) :=
  600000*(EquationRowRaw.mass r)^3+24*(EquationRowRaw.source r).length+7

theorem budget_bound (r : EquationRow.Input) : budget r ≤ uniformBudget r := by
  have h := EquationRowRaw.budget_polynomial r
  unfold budget uniformBudget
  omega

theorem producer_run (r : EquationRow.Input) : ∃ actual,
    run machine (uniformBudget r) (input r)=some actual ∧
    actual.final.tapes 128=physicalInput (EquationRow.request r) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps ≤ uniformBudget r := by
  obtain ⟨actual,ha,ht,hh,hs⟩ := framed_run r
  have hb := budget_bound r
  have hm := run_moreFuel machine (budget r) (uniformBudget r-budget r) _ actual ha
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨actual,hm,ht,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.EquationRowFramed
