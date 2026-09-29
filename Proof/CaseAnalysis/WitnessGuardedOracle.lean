import Proof.CaseAnalysis.RowsGatePair
import Proof.CaseAnalysis.WitnessNativeGuard

/-! The paid actual native-width comparison precedes the complete cold
oracle parser. Its rejecting branch does not enter the parser; both branches
retain the entire selected source bank and the original input-length field. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GuardedOracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization ExecutableInterfaces CanonicalWitnessCodec
open RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (t : ℕ):=OracleCall.tapes (t+4)
def fields {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t) : Fin 2 → Fin t:=![parser 2,length]
def parserFields {t : ℕ} (parser : Fin 3 → Fin t) : Fin 3 → Fin (t+4):=fun i=>(parser i).castAdd 4
def old {t : ℕ} (i : Fin t) : Fin (tapes t):=OracleCall.old (i.castAdd 4)
def gate (t : ℕ) : Fin (tapes t):=OracleCall.old (NativeGuard.flagSlot t)
def flagSlot (t : ℕ):=OracleCall.parserSlots (t+4) Oracle.flagSlot
def descriptorSlot (t : ℕ):=OracleCall.parserSlots (t+4) Oracle.descriptorSlot
def first {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t):=
  RecoveryFocus.machine (@OracleCall.old (t+4)) (NativeGuard.machine (fields parser length))
def second {t : ℕ} (parser : Fin 3 → Fin t):=OracleCall.machine (parserFields parser)
def machine {t : ℕ} (parser : Fin 3 → Fin t) (length : Fin t):=
  CloseoutRowsGateColdPair.machine (first parser length) (second parser) (fun scanned=>scanned (gate t))
def passed (R : ℕ) (x bits : List Bool):=
  decide (R ≤ x.length) && (decodeBooleanCircuit R (value bits)).isSome

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.GuardedOracle
