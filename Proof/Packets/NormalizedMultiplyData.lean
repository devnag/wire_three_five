import Proof.Packets.MaskProductReady
import Proof.Packets.MaskProductOuter
import Proof.Packets.PhysicalParityScan
import Proof.Packets.NormalizerCold

/-! Fixed physical ports for support-product production followed by cold
ordered normalization. Operands, counts, and two width templates are the
only nonconstant entry data. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch

def productSlots : Fin 9→Fin 30 := ![24,25,26,0,3,27,28,13,29]
def extras (B : Nat) (left right : List (List Bool)) : Fin 6→List Bool :=
  ![UnaryTemplate.tape B,left.flatten,right.flatten,CompareMachine.word right.length,
    CompareMachine.word left.length,[]]
def data (B : Nat) (left right raw : List (List Bool)) : Fin 30→List Bool :=
  fun i=>Fin.addCases (m:=24) (n:=6) (motive:=fun _=>List Bool) (NormalizeCold.data B raw) (extras B left right) i
noncomputable def productMachine := RecoveryFocus.machine productSlots MaskProduct.readyMachine
noncomputable def normalizeMachine := TapeEmbedding.machine 6 NormalizeCold.machine
noncomputable def machine := Composition.machine productMachine normalizeMachine

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
