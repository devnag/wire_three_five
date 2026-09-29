import Proof.SourceAssembly.SourceFactorSelModes

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.DescF
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierPipeline SourceInterfaces
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest
open Desc (Kind gdesc cp sysW sysCost dT copy_step pad_nil read_true read_blank stop_step sys_run flagS flagO)
noncomputable section

/-! ## The machine -/

/-! ## Per mode -/

section

end


end
end NearCubicWires.SourceFactorSel.DescF
