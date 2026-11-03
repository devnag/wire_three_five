import Proof.SourceAssembly.SourceRequestSelOrigCost
import Proof.SourceAssembly.SourceRequestSelWinLoop
import Proof.SourceAssembly.SourceFactorSelSysCost

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
namespace NearCubicWires.SourceRequest.SelLoopCost
open PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.SourceRequest.FactorLoop (factorsAt factorsAt_le)
open NearCubicWires.SourceFactorSel

/-! ## Segments of a flat map -/

/-! ## The constants -/

def slotE (a : DecompositionAlgorithm) : Nat :=
  max (max (SysCost.thrE a.degree) (SelOrigCost.thrOE a)) (max SysCost.symE 2)

def slotC (a : DecompositionAlgorithm) : Nat :=
  SysCost.thrC a.degree a.coefficient + SelOrigCost.thrOC a + SysCost.symC + 30004

def loopC (a : DecompositionAlgorithm) : Nat := 4 * slotC a + 1004

section gen

end gen

/-! ## The loop -/

end NearCubicWires.SourceRequest.SelLoopCost
end

