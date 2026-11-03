import Proof.Assembly.PhaseInput

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option quotPrecheck false
namespace PCJ30aa6f1b7c2a4221_.SelectedConstruction
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary P1TopDown
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open CloseoutRowsOriginalSchedule CloseoutRowsEstimatorCoefficients.Stream
open PCJ374c44bb8b7f47d9_ (branchFuel)
open PCJ374c44bb8b7f47d9_.S (ports heads bank mode)
open PCJda54a286946142d3_BranchPhases (offset tapes offset_ge fresh_lt body)
open ControllerSelectedContinuation (bodyTapes)
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
 (hp : P1Independent.CappedLegalAdmission.passed sources p
  (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
  (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
 (site : Bool → Phase → Σ states, Machine (bodyTapes sources p k r scratch) states)
 (remainingFuel : Nat) (width : Phase → Nat)
local notation "H0" => heads sources p k r scratch
local notation "A0" => bank sources p den hden k r scratch n x bits hp
local notation "M0" => mode sources p den hden k r scratch n x bits hp
local notation "clk" => PolynomialClock.ordinaryClock k
local notation "oracle" => C10TotalDecode.oracleOf sources k clk p.degree n bits
local notation "PI" => PhaseConstruction.Input sources p k den r scratch clk n x oracle bits site M0


end
end PCJ30aa6f1b7c2a4221_.SelectedConstruction
