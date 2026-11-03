import Proof.Wire_3_5.FinalPass.S5TNum2
import Proof.Wire_3_5.FinalPass.ThrSz6Base
import Proof.Wire_3_5.FinalPass.FpInLenBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4OBase

/-! # S5-THR, part 37: the THR half's constants and a request's facts (P3:3114-3115, 3170-3181)

The THR half's parameters in the paper's order of choice: the degrees on `l` alone (**`DtT`**, the `thrNumsPoly`
degree at the cap's degree; **`Hd`**, at least every piece's degree; **`Zx`**, **`Dl`**, the half's exponent), the
coefficient on `F` (**`KtT`**, **`c0T`**, at least every piece's coefficient). At a THR request: **`call_facts`**
(the call's precondition: carriers `≤ 2`, descriptions `≤ (n+1)^{26}`, the carriers' envelope, the star
hypotheses), **`one_le_n`**, **`vals_le`** (every W6 number `≤ K_t·(n+1)^{D_t}`), **`natWord_le_reqW`** (the codes
inside the request word).

Paper quantity of the main types: the call's numbers polynomial in `n` with the degree fixed before the gate
(P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

section Par

end Par

section Req

end Req

/-- **The codes lie inside the request word.** -/
theorem natWord_le_reqW (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    (∀ x ∈ codes, (RepairRepresentation.natWord x).length ≤ (PrimAsm.Data.reqW n mb codes cc tl).length) ∧
    (∀ y ∈ cc, (RepairRepresentation.natWord y).length ≤ (PrimAsm.Data.reqW n mb codes cc tl).length) := by
  unfold PrimAsm.Data.reqW RepairRepresentation.natListWord
  simp only [List.length_append, List.length_flatMap]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have := List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩ :
      (RepairRepresentation.natWord x).length ∈ codes.map (fun c => (RepairRepresentation.natWord c).length))
    omega
  · have := List.le_sum_of_mem (List.mem_map.2 ⟨y, hy, rfl⟩ :
      (RepairRepresentation.natWord y).length ∈ cc.map (fun c => (RepairRepresentation.natWord c).length))
    omega

theorem nbl_le_natWord (x : ℕ) : natBitLength x ≤ (RepairRepresentation.natWord x).length := by
  rw [PrimAsm.ParseNat.natWord_length]; omega

end NearCubicWires.WireExponent3_5.FinalPass.S5T
