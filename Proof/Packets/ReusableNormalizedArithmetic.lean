import Proof.Packets.ReusableArithmeticCleanup
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerCold
import Proof.Packets.NormalizedAdditionData

/-! The two fixed normalized arithmetic programs as reusable accumulator
transactions. All words, including reserved zero backing, match on reentry. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization

def data (B : Nat) (left right : List (List Bool)) : Fin 30 → List Bool :=
  NormalizedMultiply.data B left right []
def state (B R : Nat) (left right : List (List Bool)) : Fin 34 → List Bool :=
  bank R (padded R (data B left right))

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
