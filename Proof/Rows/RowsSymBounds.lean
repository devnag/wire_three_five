import Proof.Rows.RowsSymVerdict
import Proof.MachineModel.BlockPolyBound

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline
noncomputable section

theorem pb_sq {v m c d : Nat} (h : PolyBounded v m c d) : PolyBounded (v^2) m (c*c) (d+d) := by
  rw [pow_two]; exact h.mul h

/-- `a+1+b` (sequential composition). -/
theorem J {m a b ca cb da db : Nat} (ha : PolyBounded a m ca da) (hb : PolyBounded b m cb db) :
    PolyBounded (a+1+b) m (ca+1+cb) (max (max da 0) db) :=
  PolyBound.add (PolyBound.add ha (const 1 m 0)) hb

/-! ## Encoding facts: every SYM size is bounded by the native word, which is bounded by `|input|` -/

/-! ## C3(e) for SYM: every numeric premise of the SYM cell, at request-sized parameters -/

end
end RowsConstruction.SymBounds
