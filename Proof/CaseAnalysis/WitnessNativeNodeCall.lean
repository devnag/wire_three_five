import Proof.CaseAnalysis.WitnessOracleCapCall
import Proof.PCP.PCPPNativeCounterNodesDock
import Proof.PCP.PCPPNativeClauseQueryForward
import Proof.Amplification.RecoveryAllCodeLayout

/-! Reuse the original complete node emitter on the measured nine-field
bank. The cap checker preserves these fields, so no metadata scan is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeNodeCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old {t : ℕ} (i : Fin t) : Fin (t+363):=i.castAdd 363
def bank {t : ℕ} (counter : Fin 75→Fin t) : Fin 438→Fin (t+363):=
  Fin.addCases (m:=75) (n:=363) (motive:=fun _=>Fin (t+363))
    (fun i=>old (counter i)) (fun i=>i.natAdd t)
def slots {t : ℕ} (counter : Fin 75→Fin t):=bank counter ∘ PCPPNativeCounterNodes.slots

def machine {t : ℕ} (counter : Fin 75→Fin t):=RecoveryFocus.machine (slots counter) PCPPNativeClauseOracle.machine

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeNodeCall
