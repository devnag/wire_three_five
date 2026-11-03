import Proof.CaseAnalysis.RowsOriginalClauseLoop
import Proof.Rows.FinalNativeResidueCallback
import Proof.Rows.OffsetEmitter
import Proof.Rows.ThresholdData

/-! Physically compose all four selected TOP blocks with the final unscaled
binary offset append on the same growing output tape. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CoefficientRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
open PCJ45bee56da9f34d5a_FourfoldPowerData
noncomputable section

def extra (p w U o :Nat):Fin 12→List Bool:=fun i=>
 PCJ45bee56da9f34d5a_OffsetEmitter.cold (PCJ45bee56da9f34d5a_OffsetEmitter.palette p w o) U [] (i.castAdd 1)
def bank (d :Data) (a B p w F U v o :Nat) (out :List Bool):Fin 122→List Bool:=
 Fin.addCases (m:=110) (n:=12) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_FourfoldPowerCell.bank (d.words.flatMap frame) d.digits d.count a B p w F U v out)
  (extra p w U o)



end
end PCJ45bee56da9f34d5a_CoefficientRun
