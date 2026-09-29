import Proof.SourceAssembly.SourceRestLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.InitPost
noncomputable section

/-! ## 1. The docks -/

def rc79 : Fin 79 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 0 else if j.val = 47 then 18 else if j.val = 77 then 12 else 32 + j.val, by
    have := j.isLt; split_ifs <;> omega⟩
def sl57 : Fin 57 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 0 else if j.val = 1 then 18 else if j.val = 49 then 21 else if j.val = 55 then 17
    else 111 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def un43 : Fin 43 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 2 else if j.val = 1 then 3 else if j.val = 2 then 1 else if j.val ≤ 6 then 10 + j.val
    else if j.val ≤ 40 then 282 + j.val else if j.val = 41 then 4 else 5, by
    have := j.isLt; split_ifs <;> omega⟩


macro "injv2" : tactic => `(tactic| (
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [rc79, sl57, un43] at hv
  apply Fin.ext
  split_ifs at hv <;> omega))



/-! ## 2. The machine, the input, the cost -/

/-! ## 3. The copy of `1^b`, padded off its source -/

/-! ## 4. The run -/

end
end NearCubicWires.SourceConstruction.InitPost
end
