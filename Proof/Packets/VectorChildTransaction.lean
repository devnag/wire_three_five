import Proof.Packets.VectorChildLookup
import Proof.Packets.VectorChildArithmetic

/-! Closed physical child-contribution transaction. Read the indexed resident
child into the left operand, multiply by the resident right delta packet, and add that term to the saved
parent accumulator. The source bank and physical child index are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildTransaction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots : Fin 36→Fin 39 := Fin.addCases (m:=34) (n:=2) (motive:=fun _=>Fin 39)
  (fun i=>i.castAdd 5) (![37,38])
def lookup := TapeEmbedding.machine 2 ArithmeticLookup.machine
def arithmetic := RecoveryFocus.machine slots VectorChildArithmetic.machine
def machine := Composition.machine lookup arithmetic


end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildTransaction
