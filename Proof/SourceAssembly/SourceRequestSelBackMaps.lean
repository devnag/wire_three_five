import Proof.SourceAssembly.SourceRequestSelFrontB
import Proof.SourceAssembly.SourceRequestCurClausePart
import Proof.SourceAssembly.SourceFactorSelSlots4
import Proof.SourceAssembly.SourceFactorSelCoefBridge
import Proof.SourceAssembly.SourceFactorSelModes
import Proof.SourceAssembly.SourceFactorSelSlot
import Proof.SourceAssembly.SourceLiteralGuard
import Proof.SourceAssembly.SourceRequestCoordBridge
import Proof.SourceAssembly.SourceFactorSelHdrBlock
import Proof.SourceAssembly.SourceFactorSelCoefR

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelBack
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairRepresentation
open NearCubicWires.SourceRequest.SelFront
noncomputable section

section
variable {mode : Bool} {da : DecompositionAlgorithm} {n0 : Nat}
  {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}
variable (P : FactorLoop.FactorProducer mode da pcpp)



/-- A slot's `k`-th input port (`k < 17`). -/
def inPort (i k : Nat) : Nat :=
  if k < 4 then 1206 + 4 * i + k
  else ([129, 141, 103, 104, 19, 29, 30, 21, 22, 23, 24, 31, 42] : List Nat).getD (k - 4) 0

theorem inPort_lt : ∀ i < 4, ∀ k < 17, inPort i k < 1300 := by decide

end
end
end NearCubicWires.SourceRequest.SelBack

