import Proof.Packets.SrcStartBank
import Proof.SourceAssembly.SourceFactorSelItem4AtS
import Proof.SourceAssembly.SourceRequestSelDockSym

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost NearCubicWires.SourceFactorSel.AtS
namespace NearCubicWires.SourceFactorSel.G7Fam
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-! ## 1. The loop and the words-stage sources without the producer's PCPP -/

section pcpp

end pcpp

/-! ## 2. The family -/

section S

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-! ## 3. The bridge to `AtS.hG7_of` -/

end S

end
end NearCubicWires.SourceFactorSel.G7Fam
end

