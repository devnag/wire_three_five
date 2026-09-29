import Proof.SourceAssembly.SourceRequestFactorLoop
import Proof.SourceAssembly.SourceRequestThrParity
import Proof.SourceAssembly.SourceSingletonRequest
import Proof.SourceAssembly.SourceTopNative

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization SupplierPipeline CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.Gen.SupportFrame

end NearCubicWires.SourceRequest.Gen.SupportFrame


namespace NearCubicWires.SourceRequest.Gen.ChainIn

theorem addCases_nil {m n : Nat} (f : Fin m → List Bool) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin n => []) i
      = if h : i.val < m then f ⟨i.val, h⟩ else [] := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left, dif_pos (by simp)]; rfl
  · rw [Fin.addCases_right, dif_neg (by simp)]


end NearCubicWires.SourceRequest.Gen.ChainIn

namespace NearCubicWires.SourceRequest.ThrSystematic
open PCJd4d1d9d7d1fa4313_Production






/-! ### Stage entries -/

/-! ### The machine and its run -/


section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

end normal
end NearCubicWires.SourceRequest.ThrSystematic

