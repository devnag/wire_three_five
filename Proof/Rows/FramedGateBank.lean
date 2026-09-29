import Proof.Rows.NativeGateLoadReady
import Proof.Rows.UniformMinimumBounds

/-! Fixed original-native traversal bank. Only isolated short gate fields
enter the gate evaluator; the full retained source stays outside its bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FramedGateBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_CellGatePalette
noncomputable section

def strict {q : Nat} (g : NormalizedThresholdGate q) : ExactThresholdGate q :=
 {weight:=g.weight,target:=g.threshold-1}
def coreBank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (fields out : List Bool) : Fin 114→List Bool :=
 Fin.addCases (m:=108) (n:=6) (motive:=fun _=>List Bool)
   (cold (words fields (List.replicate H false) q w (HardwireBudget.C w) R) U out)
   (PCJ45bee56da9f34d5a_MinimumGateCell.extra live x H)
def extras (source framed : List Bool) (H : Nat) : Fin 8→List Bool :=
 ![source,framed,List.replicate H false,List.replicate H false,List.replicate H false,
   List.replicate H false,List.replicate H false,List.replicate H false]
def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (source fields framed out : List Bool) : Fin 122→List Bool :=
 Fin.addCases (m:=114) (n:=8) (motive:=fun _=>List Bool) (coreBank live x w H R U fields out) (extras source framed H)

end
end PCJ45bee56da9f34d5a_FramedGateBank
