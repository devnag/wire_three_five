import Succinct.H2Step
import Succinct.H2SplitB

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform NearCubicGates.Close.Succinct NearCubicGates.Close.Outer

variable {q : ℕ}

/-- The loop counter fits the register capacity: `n_C ≤ capH`. -/
theorem nC_le_cap (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (hcap : capH o B ≤ cap) :
    o.circuit.nodes.length ≤ cap := by
  have h1 := (sizes_le o B).1
  have h2 := capH_ge o B
  have h3 : sizeS o B + 2 ≤ (sizeS o B + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  omega

/-- **The emission loop of `D_B`** (the near-cubic-gates paper's fixed weak machine: the fold of `Outer.substStepG` over the nodes of `C`):
`n_C` rounds of `dec iC ; nodeBody` take `MInv o B 0` to `MInv o B n_C`, within `n_C` node costs. -/
theorem emLoop (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (hK1 : Kind1OK cap o B)
    (hcap : capH o B ≤ cap) (σ : WState 4 nrH) (hI0 : MInv o B 0 σ) :
    ∃ τ, WExec cap (.whr (regH .iC) (.seq (.dec (regH .iC)) nodeBody)) σ τ
        (o.circuit.nodes.length * (readCost 5 + nIter (sizeS o B) + 20 + 4) + 1) ∧
      MInv o B o.circuit.nodes.length τ ∧ τ.val (regH .iC) = 0 := by
  have hv : ∀ u, σ.val (regH u) = VM o B 0 u := hI0.2.2.2.2.2.2.2.2.2.2.1
  have hiC : σ.val (regH .iC) = o.circuit.nodes.length := by rw [hv]; simp [VM]
  exact UnionMachine.Round.wloopE cap (regH .iC) nodeBody (readCost 5 + nIter (sizeS o B) + 20)
    o.circuit.nodes.length (fun k τ => MInv o B k τ) (nC_le_cap cap o B hcap)
    (fun k hk τ hτ _ => nodeStep cap o B hK1 k hk τ hτ hcap) σ hI0 hiC

end NearCubicGates.Close.Succinct.H2
