import Proof.SourceAssembly.SLoadRequestFrames
import Proof.Assembly.AppendOutputFrame
import Proof.Amplification.RecoveryPCPFormulaResumeForward

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.SuffixFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The framing pass of `SLoadRequestFrames`, on its own nine local tapes:
mask output, unary mask driver, framing scratch, the four retained request
fields, the growing packet-input scratch and the shared reset log. -/
def raw : Machine 9 25 := RequestFrames.machine 0 1 2 3 4 5 6 7 8

/-- The framed suffix program: the framing pass, its paid output measurement
and its paid output framer, all with numeral tape and state counts. -/
def wrapper : Machine 13 34 := AppendOutputFrame.machine raw 7

/-- The docked suffix program. -/
def machine {U : Nat} (slot : Fin 13 → Fin U) : Machine U 34 :=
  RecoveryFocus.machine slot wrapper

/-- Fuel for the suffix, in the five actual physical word lengths. -/
def cost (q n s i t : Nat) : Nat := 8 * q + 16 * (n + s + q + i + t) + 75


end
end SLoad.SuffixFrame
