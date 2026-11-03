import Proof.SourceAssembly.SourceRequestSymParity
import Proof.SourceAssembly.SourceSymmetricBound
import Proof.SourceAssembly.SourceThresholdBounds
import Proof.Circuits.DecompositionSourceRealization
import Proof.Circuits.DecompositionSourceBounds
import Proof.CaseAnalysis.RowsEstimatorDriverPower
import Proof.CaseAnalysis.RowsEstimatorParityNatural
import Proof.Circuits.ComponentwiseCircuitRestriction
import Proof.CaseAnalysis.FinalSources

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization SupplierPipeline CompilerSemantics
open NearCubicWires.SourceRequest ExecutableInterfaces NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceFactorSel.SysCost
noncomputable section

/-! ### Generic pieces -/

/-! ### SYM -/

def symC : Nat := 65536
def symE : Nat := 2

/-! ### THR -/

/-- `(D, Cc)` bound the decomposition source's degree and coefficient (at the site: its own fields, `le_rfl`). -/
def thrC (D Cc : Nat) : Nat := 4096 * (Cc * 2 ^ D + 3) ^ 2 + 2 ^ 22
def thrE (D : Nat) : Nat := 2 * D + 3

end
end NearCubicWires.SourceFactorSel.SysCost
end

