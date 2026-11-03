import Succinct.H2Split
import Succinct.H2Loop

/-!
# H2′, the whole run from the split

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer), `D_B`: `h2Prog = header ; countPass ; sizes ; emission` with
`emission = emStart ; (while iC: dec iC ; nodeBody) ; emissionEnd`. **`h2Run_of`**: the three pieces
(`PreSpec`, `PostSpec`, `CostSpec`, Succinct/H2Split.lean) and the emission loop (`emLoop`) give `H2RunSpec`: the
output stream ends as `frame (descriptor D_B)` within `h2Cost S`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform NearCubicGates.Close.Succinct NearCubicGates.Close.Outer

variable {q : ℕ}

/-- **The emission phase of `D_B`** (the near-cubic-gates paper's fixed weak machine): emission start, the loop over the nodes of `C`, and
the emission end leave `frame (descriptor D_B)` on the output stream, the port streams unchanged. -/
theorem emission_run (hE : PostSpec) (cap : ℕ) (o : OracleOutput) (B : BooleanCircuit q) (hK1 : Kind1OK cap o B)
    (hcap : capH o B ≤ cap) (σ3 σ4 : WState 4 nrH)
    (e4 : WExec cap emStart σ3 σ4 (1000000 * (sizeS o B + 2) ^ 3)) (hI : MInv o B 0 σ4) :
    ∃ τ, WExec cap emission σ3 τ (1000000 * (sizeS o B + 2) ^ 3 + 1 +
        ((o.circuit.nodes.length * (readCost 5 + nIter (sizeS o B) + 20 + 4) + 1) + 1 + 2 * cIter (sizeS o B))) ∧
      τ.st sO = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit o.circuit B).padToArity) ∧
      τ.st sW = o.word ∧ τ.st sD = PCPPNative.descriptor B := by
  obtain ⟨τL, eL, hIL, -⟩ := emLoop cap o B hK1 hcap σ4 hI
  obtain ⟨τ, eE, hO, hW, hD⟩ := hE o B cap τL hcap hIL
  exact ⟨τ, WExec.seq e4 (WExec.seq eL eE), hO, hW, hD⟩

/-- **The whole run of H2′** (the near-cubic-gates paper's fixed weak machine, `D_B`), from the split: `PreSpec` (header to
emission start), `emLoop`, `PostSpec` (emission end), and `CostSpec` (the cost class `h2Cost S`), with the
input-node case `Kind1OK` as a hypothesis, at the capacity `capH o B`. -/
theorem h2Run_of (hP : PreSpec) (hE : PostSpec) (hC : CostSpec)
    (hK1 : ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q), Kind1OK (capH o B) o B) : H2RunSpec := by
  intro o q B
  obtain ⟨σ1, σ2, σ3, σ4, e1, e2, e3, e4, hI⟩ := hP o B (capH o B) le_rfl
  obtain ⟨τ, eE, hO, hW, hD⟩ := emission_run hE (capH o B) o B (hK1 o B) le_rfl σ3 σ4 e4 hI
  have hc := hC (sizeS o B) o.circuit.nodes.length (by have := (sizes_le o B).1; omega)
  exact ⟨capH o B, τ, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2)
    (WXExec.seq e3 (WXExec.wm eE)))) (by omega), hO, hW, hD⟩

end NearCubicGates.Close.Succinct.H2
