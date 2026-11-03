import Proof.SourceAssembly.SourceFactorSelWordsLayout

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-- The copies stage's five sources: native, support, TOP, `1^q`, `1^K`. -/
def cw (a : DecompositionAlgorithm) (r : Request) : Fin 5 → List Bool :=
  ![r.nativeWord, r.supportWord a, r.topWord a, List.replicate r.q true,
    List.replicate (normalizedLiveCount r.q r.liveScale) true]

section stages

/-! ## Stage 1: the copies -/

/-! ## Stage 2: the occurrence count -/

/-! ## Stage 3: lead ; mask ; frame (the framed mask word) -/

/-! ## Stage 4: the index block (P's start bank ; the accepted index run) -/

end stages

end
end NearCubicWires.SourceFactorSel.Words

