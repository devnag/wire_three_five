import Proof.SourceAssembly.SourceRestBack

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- Close a value (in)equality: `simp`, then `omega` if anything is left. -/
macro "vsimp" : tactic => `(tactic| (first | (simp; done) | (simp; omega) | omega))

/-- The slope's cost. -/
def slopeCost (L Mb Ms : Nat) : Nat :=
  (1+1+1+1+1) + 1 + (((1+1+1+1+1) + 1 + (2 * (if 3 < L then Mb else Ms) + 6)) + 2)

/-- The first three stages' cost. -/
def stagesCost {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (r : Request) : Nat :=
  (4 * (r.input a).length + 4) + 1 + (se.cost r + 1 + sp.cost r)

/-- The back half's cost. -/
def backCost {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (r : Request) (Rc w q L Mb Ms : Nat) : Nat :=
  stagesCost se sp r + 1 + (Prologue.f6FullCost Rc (vE r) (vP r) w q + 1 + slopeCost L Mb Ms)

section

end

end
end NearCubicWires.SourceConstruction.Rest
end
