import Proof.SourceAssembly.SourceFactorSelWordsHostRun
import Proof.Packets.SourceResidentCopies
import Proof.Packets.SourceResidentOccCount
import Proof.SourceAssembly.SLoadCore
import Proof.SourceAssembly.SourceFactorSelItem4Bank
import Proof.SourceAssembly.SourceFactorSelItem4Stages
import Proof.SourceAssembly.SourceFactorSelItem4Top
import Proof.SourceAssembly.SourceFactorSelRunBound

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
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open SourceInterfaces RepairSource.VerifierDecoding NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-- The six loop field ports the words stage reads: `fslot 17, 15, 23, 19, 21, 29`. -/
def srcIdx : Fin 6 → Fin 31 := ![17, 15, 23, 19, 21, 29]

section wr

end wr

end
end NearCubicWires.SourceFactorSel.WordsHost

