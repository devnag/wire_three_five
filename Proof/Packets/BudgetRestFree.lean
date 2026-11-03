import Proof.Packets.BudgetRefill3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section

/-! ## The `Rc`-free rest, split into its owners' pieces -/

theorem restFree_eq {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (g7cost : Nat → Nat) (rq : Request) (w q L Mb Ms j : Nat) :
    Rest.restCost se sp g7cost rq 0 w q L Mb Ms j =
      g7cost (j+1) + (se.cost rq + sp.cost rq) +
        (CloseoutRowsCountBinary.budget (vE rq) + CloseoutRowsCountBinary.budget (vP rq)) +
        (CompetitorDenominator.budget (natBitLength (vE rq)) w q + 4*(rq.input a).length + 6*w + 2*q + 4*j +
          2*(if 3 < L then Mb else Ms) + 100) := by
  simp only [Rest.restCost, Rest.backCost, Rest.stagesCost, Prologue.f6FullCost, Prologue.f6Cost, Rest.slopeCost,
    Rest.cursorCost]
  omega

theorem restFree_inClasses {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (g7cost : Nat → Nat) (rq : Request) (w q L Mb Ms j : Nat)
    {dP hT hS m L' n qn c1P c1T c1S c2P c2T c2S c3P c3T c3S xC : Nat}
    (hg7 : InClasses dP hT hS m L' n qn c1P c1T c1S (g7cost (j+1)))
    (hst : InClasses dP hT hS m L' n qn c2P c2T c2S (se.cost rq + sp.cost rq))
    (hcb : InClasses dP hT hS m L' n qn c3P c3T c3S
      (CloseoutRowsCountBinary.budget (vE rq) + CloseoutRowsCountBinary.budget (vP rq)))
    (hpoly : CompetitorDenominator.budget (natBitLength (vE rq)) w q + 4*(rq.input a).length + 6*w + 2*q + 4*j +
      2*(if 3 < L then Mb else Ms) + 100 ≤ xC*(n+1)^dP) :
    InClasses dP hT hS m L' n qn (c1P + c2P + c3P + xC) (c1T + c2T + c3T + 0) (c1S + c2S + c3S + 0)
      (Rest.restCost se sp g7cost rq 0 w q L Mb Ms j) := by
  rw [restFree_eq]
  exact ((hg7.add hst).add hcb).add (InClasses.poly hpoly le_rfl)

end
end NearCubicWires.SourceBudget
end

