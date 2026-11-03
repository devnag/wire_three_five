import Proof.SourceAssembly.SLoadSuffixFrame

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Tail
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The tail program: the existing raw framer, docked at the packet's own
certified output slot, a retained unary length driver, a zero-backed
destination slot and a paid rewind log. Five states, four slots, no request
in scope. -/
noncomputable def machine {U : Nat} (src drv dst log : Fin U) : Machine U 5 :=
  MaskFrame.machine src drv dst log


end
end SLoad.Tail
