import Proof.SourceAssembly.SourceRestBackRun
import Proof.SourceAssembly.SourceFactorSelRunBound

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceFactorSel.Item4
noncomputable section

section defs

end defs

section main
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {mode : Bool} {a : DecompositionAlgorithm}

/-- **Its per-call cost** (Rc-free whenever `costS`, `costW` are). -/
def g7Cost (costS costW : Nat → Nat) (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target m : Nat) : Nat :=
  costS m + 1 + (FactorLoop.cost P L target (factorsAt coordinate ph ci m) + 1 + costW m)

end main

end
end NearCubicWires.SourceFactorSel.Item4
end

