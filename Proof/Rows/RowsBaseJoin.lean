import Proof.Rows.VerdictFinish
import Proof.Rows.FourfoldBaseRun
import Proof.Rows.ScalarReplace

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.BaseJoin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. The layout -/




/-! ## 2. The two identities that make the join a plain copy -/

/-- `FourfoldBaseRun`'s accumulator port 9 holds `scalar U (w+2) a`. -/
theorem base_port9 (source : List Bool) (digits : Fin 4 → Nat) (N v w C U a : Nat) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source digits N v w C U a 9 =
      MatrixScoreWeight.scalar U (w+2) a := by
  simp [PCJ45bee56da9f34d5a_FourfoldBaseCell.bank, PCJ45bee56da9f34d5a_DigitBaseInput.bank,
    PCJ45bee56da9f34d5a_CircuitBaseInput.bank, PCJ45bee56da9f34d5a_CircuitBaseInput.caps,
    PCJ45bee56da9f34d5a_SelectedBase.bank, PCJ45bee56da9f34d5a_SelectedBase.core,
    PCJ45bee56da9f34d5a_CanonicalBaseInput.input, PCJ45bee56da9f34d5a_CanonicalBaseInput.ready,
    PCJ45bee56da9f34d5a_CanonicalBaseInput.caps, ExtIncidence.NativeFanout.reusableInput,
    PCJ45bee56da9f34d5a_CanonicalBaseCell.words, Fin.addCases, ZeroPadding.pad_zero]

/-! ## 3. The three stages -/

end
end RowsConstruction.BaseJoin
