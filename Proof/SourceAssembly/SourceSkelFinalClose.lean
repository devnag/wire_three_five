import Proof.SourceAssembly.SourceFactorSelSeamSite
import Proof.SourceAssembly.SourceRequestSelLoopSite
import Proof.SourceAssembly.SourceStepsSite

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
open NearCubicWires.SourceSteps
namespace NearCubicWires.SourceSkeleton.Final
noncomputable section

section close

set_option hygiene false in
local notation "𝔛" => NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector
set_option hygiene false in
local notation "𝔊" => NearCubicWires.SourceFactorSel.G7W.G7Site selector (NearCubicWires.SourceFactorSel.OnsetFin.xtraFin selector)
set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector 𝔛 mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector 𝔛 𝔊 mask packets rows)) (FirstW.firstW selector 𝔛 𝔊 mask packets rows)

end close

end
end NearCubicWires.SourceSkeleton.Final
end

