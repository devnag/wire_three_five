import Proof.SourceAssembly.SourceRequestCurSpec
import Proof.SourceAssembly.SourceRequestCurComp
import Proof.CaseAnalysis.RowsEstimatorCoefficientsProductRead

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurContract
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
noncomputable section

/-! ## Ports -/

def rhoT : Fin 128 := 23

/-- The multiplier of monomial `m`'s symbolic record (`0` past the end). -/
def rhoOf (σ : Option Sel) : ℚ := (σ.map Sel.rho).getD 0

/-- The record width of the multiplier: `rho ∈ {1, -1, 1/2}` has `|num|, den < 2^2`. -/
def rhoW : Nat := 2

/-- One size bound for every phase (`N ≤ curBig`, every block length and digit below it). -/
def curBig (JL JR : Nat) : Nat :=
  64 * ((JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)))

/-- One cost bound for every phase (source polynomial in `JL + JR`). -/
def curCost (JL JR : Nat) : Nat := 64 * curBig JL JR

/-! ## Blank-port identities -/

/-! ## Proof helpers for cursor builders (scratch-length invariant, per-slot `∀`) -/

/-! ## Docked form -/

end
end NearCubicWires.SourceRequest.CurContract

