import Succinct.H2SplitB
import Succinct.L10Node

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

variable {q : ℕ}

/-- The registers `emissionEnd` reads, at the loop's exit (the near-cubic-gates paper's fixed weak machine, `D_B`): `o_C`, `|B| − 1`, `o_B`,
the padding `q − (|accI n_C| + 1)`, the output index `|accI n_C|`, and the clean accumulator `x`. -/
theorem post_vals (o : OracleOutput) (B : BooleanCircuit q) (σ : WState 4 nrH)
    (hM : MInv o B o.circuit.nodes.length σ) :
    σ.val (regH .x) = 0 ∧ σ.val (regH .oC) = o.circuit.output.val ∧
      σ.val (regH .nB1) = B.nodes.length - 1 ∧ σ.val (regH .oB) = B.output.val ∧
      σ.val (regH .pd) = q - (szv o B + 1) ∧ σ.val (regH .sz) = szv o B := by
  have hv : ∀ u, σ.val (regH u) = VM o B o.circuit.nodes.length u := hM.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hv] <;> simp [VM, V3, V2, V1]

/-- The register bounds and the capacity `emissionEnd_spec` asks for, at the loop's exit (the near-cubic-gates paper's fixed weak machine,
`D_B`): every read value is at most `S = sizeS o B`, the output index at most `(S + 2)²`, and the capacity covers twice
the emitted word plus `1000 (S + 2)²`. -/
theorem post_bounds (o : OracleOutput) (B : BooleanCircuit q) (cap : ℕ) (hcap : capH o B ≤ cap) :
    o.circuit.output.val ≤ sizeS o B ∧ B.nodes.length - 1 ≤ sizeS o B ∧ B.output.val ≤ sizeS o B ∧
      q - (szv o B + 1) ≤ sizeS o B ∧ szv o B ≤ (sizeS o B + 2) ^ 2 ∧
      2 * (hdrD o B ++ (accI B o.circuit o.circuit.nodes.length).1.flatMap PCPPRequestNodeSchema.native).length +
        1000 * (sizeS o B + 2) ^ 2 ≤ cap := by
  obtain ⟨hzC, hzB, hzq, -⟩ := sizes_le o B
  have hoC := o.circuit.output.isLt
  have hoB := B.output.isLt
  have hol := out_le o B o.circuit.nodes.length le_rfl
  have h4 := sq4 (sizeS o B)
  refine ⟨by omega, by omega, by omega, by omega, szv_le o B, ?_⟩
  unfold capH at hcap
  omega

theorem postSpec_of (hE : EndOutSpec) : PostSpec := by
  intro o q B cap σ hcap hM
  obtain ⟨hx, hoC, hn1, hoB, hpd, hsz⟩ := post_vals o B σ hM
  obtain ⟨boC, bn1, boB, bpd, bsz, bcap⟩ := post_bounds o B cap hcap
  obtain ⟨τ, e, hO, hW, hD⟩ := emissionEnd_spec cap (n := q) σ hM.cbz hx (ofl o.circuit) hM.2.2.2.2.1
    hM.2.2.2.2.2.1 (sizeS o B) (by rw [hoC]; exact boC) (by rw [hn1]; exact bn1) (by rw [hoB]; exact boB)
    (by rw [hpd]; exact bpd) (by rw [hsz]; exact bsz)
    (hdrD o B ++ (accI B o.circuit o.circuit.nodes.length).1.flatMap PCPPRequestNodeSchema.native)
    hM.2.2.2.2.2.2.2.2.1 hM.2.2.2.2.2.2.2.2.2.1 bcap
  refine ⟨τ, e, ?_, by rw [hW]; exact hM.1, by rw [hD]; exact hM.2.2.1⟩
  rw [hO, hoC, hn1, hoB, hpd, hsz]
  exact hE o B

end NearCubicGates.Close.Succinct.H2
