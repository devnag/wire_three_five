import Proof.SourceAssembly.SourceFactorSelWordsRunA

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

section stages
variable {w C k : Nat} (a : DecompositionAlgorithm) (r : Request) (MB : List Bool) (Rc : Nat)

/-! ## Stage 6: the K template -/

/-! ## Stage 7: the pool block (P's start bank ; the accepted cache run) -/


/-- The pool block's two bank outputs, by value. -/
def q98 (a : DecompositionAlgorithm) (k : Nat) : Nat := (Item4.plOut a k 98).val
def q224 (a : DecompositionAlgorithm) (k : Nat) : Nat := (Item4.plOut a k 224).val
/-- The pool block's dock. -/
def M7 (w : Nat) (a : DecompositionAlgorithm) (k : Nat) := m7 w (Cold.tapes a) k (q98 a k) (q224 a k)


/-! ## Stage 8: the child-list length -/

/-! ## Stages 9–10: the bare meta words -/

end stages

end
end NearCubicWires.SourceFactorSel.Words

