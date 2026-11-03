import Succinct.H2Split
import Succinct.H2SplitB
import Succinct.H2Main
import Succinct.H2CopyLoop
import Succinct.PointLoop

/-!
# H2′: the emitted word and the cost class

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer), `D_B`: "Substituting `O_{B_pf}` for every oracle gate and negating
the output gives the outer verifier `D_B`"; `D_B` is computed in time polynomial in its inputs.
* **`h2_cost_le`** / **`costSpec`**: header + count pass + sizes + emission start + `n ≤ S` node iterations +
  emission end fit in `h2Cost S = 10^10 (S+2)^7` (`H2Split.CostSpec`).
* **`endOut`** / **`endOutSpec`**: the stream the emission writes (header of `D_B`, the fold's nodes, the negated image
  of `C`'s output, the padding, the output index, the closing cell) is `frame (descriptor D_B)`
  (`H2SplitB.EndOutSpec`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

/-- One node iteration of the emission loop is `O((S+2)^5)` (the near-cubic-gates paper's fixed weak machine, `D_B`: polynomial time). -/
theorem nIter_le (S : ℕ) :
    nIter S ≤ 100000000 * (S + 2) ^ 5 + 100000000 * (S + 2) ^ 4 + 1000000 * (S + 2) ^ 2 + 1000004 * (S + 2) +
      1000000 := by
  unfold nIter oIter cpIter cIter
  have h1 : (S + 1) * (100000000 * (S + 2) ^ 4 + 1000000 + 4) ≤
      (S + 2) * (100000000 * (S + 2) ^ 4 + 1000000 + 4) := Nat.mul_le_mul_right _ (by omega)
  have e : (S + 2) * (100000000 * (S + 2) ^ 4 + 1000000 + 4) = 100000000 * (S + 2) ^ 5 + 1000004 * (S + 2) := by
    ring
  omega

/-- **H2′'s cost class** (the near-cubic-gates paper's fixed weak machine, `D_B`: computed in time polynomial in its inputs): header + count
pass + sizes + emission start + `n ≤ S` node iterations + emission end fit in `h2Cost S = 10^10 (S+2)^7`. -/
theorem h2_cost_le (S n : ℕ) (hn : n ≤ S) :
    headCost S + cntCost S + sizesCost S + 1000000 * (S + 2) ^ 3 + n * (readCost 5 + nIter S + 20 + 4) +
      2 * cIter S + 100 ≤ h2Cost S := by
  have hR : readCost 5 = 490000 := by unfold readCost; norm_num
  have hI := nIter_le S
  have hN : n * (readCost 5 + nIter S + 20 + 4) ≤ (S + 2) * (100000000 * (S + 2) ^ 5 + 100000000 * (S + 2) ^ 4 +
      1000000 * (S + 2) ^ 2 + 1000004 * (S + 2) + 1490024) := Nat.mul_le_mul (by omega) (by omega)
  have e : (S + 2) * (100000000 * (S + 2) ^ 5 + 100000000 * (S + 2) ^ 4 + 1000000 * (S + 2) ^ 2 +
      1000004 * (S + 2) + 1490024) = 100000000 * (S + 2) ^ 6 + 100000000 * (S + 2) ^ 5 + 1000000 * (S + 2) ^ 3 +
      1000004 * (S + 2) ^ 2 + 1490024 * (S + 2) := by ring
  have hX2 : 2 ≤ S + 2 := by omega
  unfold headCost cntCost sizesCost cIter h2Cost
  generalize S + 2 = X at hN e hX2 ⊢
  have p1 : X ≤ X ^ 7 := Nat.le_self_pow (by norm_num) X
  have p2 : X ^ 2 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p3 : X ^ 3 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p4 : X ^ 4 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p5 : X ^ 5 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p6 : X ^ 6 ≤ X ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have p0 : 1 ≤ X ^ 7 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **H2′'s cost class, ** (`H2Split.CostSpec`; the near-cubic-gates paper's fixed weak machine, `D_B`). -/
theorem costSpec : CostSpec := h2_cost_le

/-- **The emitted word is `frame (descriptor D_B)`** (the near-cubic-gates paper's fixed weak machine, `D_B`: "Substituting `O_{B_pf}` for
every oracle gate and negating the output gives the outer verifier `D_B`", size-padded to its arity): the header of
`D_B`, the fold's nodes, the negation of `o_C`'s image, the `q − (|fold| + 1)` padding nodes, the output index
`|fold|`, the closing cell. -/
theorem endOut (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q) :
    marks (hdrD o B ++ (accI B o.circuit o.circuit.nodes.length).1.flatMap PCPPRequestNodeSchema.native ++
        PCPPRequestNodeSchema.native
          (BooleanNode.not (posF (ofl o.circuit) o.circuit.output.val (B.nodes.length - 1) B.output.val) :
            BooleanNode q) ++
        (List.replicate (q - (szv o B + 1)) (BooleanNode.const false : BooleanNode q)).flatMap
          PCPPRequestNodeSchema.native ++
        natWord (szv o B)) ++ [false] =
      RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit o.circuit B).padToArity) := by
  rw [NearCubicGates.Close.Succinct.frame_eq_marks', descriptor_D B o.circuit, szv_eq,
    ← posM_posF B o.circuit o.circuit.output.val o.circuit.output.isLt.le]
  simp only [hdrD, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- **The emitted word, ** (`H2SplitB.EndOutSpec`; the near-cubic-gates paper's fixed weak machine, `D_B`). -/
theorem endOutSpec : EndOutSpec := fun o _ B => endOut o B

end NearCubicGates.Close.Succinct.H2
