import Proof.Rows.Plan

/-! Evaluating the original gate on the physically readable minimizing assignment
is exactly its residual-constant flag; no threshold or weight rewrite is needed. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_MinimumAssignment
open NearCubicWires NearCubicWires.SupplierPipeline
open NearCubicWires.CompilerSemantics NearCubicWires.ThresholdCompiler
noncomputable section

def input {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q))
    (x : BitInput q) : BitInput q := fun i => if i ∈ live then decide (g.weight i < 0) else x i

end
end PCJ45bee56da9f34d5a_MinimumAssignment
