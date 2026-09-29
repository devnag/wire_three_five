import Proof.SourceAssembly.SourceFactorSelWordsHostLay
import Proof.SourceAssembly.SourceRequestConsumer

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
open NearCubicWires.SourceFactorSel.Words
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

section res

/-- Unfold the layout predicates and close a linear goal. -/
macro "lz" : tactic => `(tactic| (simp only [HostLay.IsTgt, HostLay.Blank, HostLay.NSv, HostLay.P0, HostLay.B, HostLay.tc] at *; omega))

section facts

end facts

end res

end
end NearCubicWires.SourceFactorSel.WordsHost

