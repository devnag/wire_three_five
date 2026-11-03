import Proof.CaseAnalysis.RowsModeCacheReuseRun
import Proof.CaseAnalysis.RowsModeCacheSource
import Proof.Supplier.EquationZeroField

/-! The original ordinary mode-cache machine reuses the physically generated
common reserve. Its private-capacity driver is supplied by that actual reserve
producer; the machine never assumes a separately generated reuseCapacity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheCommon
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] reuseMachine

noncomputable def delta := Composition.machine (reuseMachine 1) (reuseMachine 2)
attribute [local irreducible] delta

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheCommon
