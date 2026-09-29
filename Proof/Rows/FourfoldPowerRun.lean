import Proof.Rows.FourfoldPowerCell
import Proof.Rows.FourfoldPowerData

/-! Four guarded actual selected coefficient calls, with one power update per
active circuit and restored circuit-count cursor. Absent circuits emit nothing. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FourfoldPowerRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data words_length)
open PCJ45bee56da9f34d5a_FourfoldPowerData
open PCJ45bee56da9f34d5a_FourfoldPowerCell (bank heads)
noncomputable section


end
end PCJ45bee56da9f34d5a_FourfoldPowerRun
