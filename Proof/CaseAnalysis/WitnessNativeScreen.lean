import Proof.CaseAnalysis.WitnessNativeMeasured

/-! One post-decoder stream/counter execution supplies the exact full
oracle-size screen. Its measured native fields survive for the gated
node and faithful PCPP-source continuation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fields : Fin 2 → Fin 125:=NativeMeasured.slots ∘ (![72,32] : Fin 2 → Fin 75)
def slots (G : ℕ) (i : Fin 75):=OracleCap.Call.old G (NativeMeasured.slots i)
def flagSlot (G : ℕ):=OracleCap.Call.flagSlot G fields
def first (G : ℕ):=TapeEmbedding.machine (OracleCap.Call.extra G) NativeMeasured.machine
def second (G : ℕ):=OracleCap.Call.machine G fields
def machine (G : ℕ):=Composition.machine (first G) (second G)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
