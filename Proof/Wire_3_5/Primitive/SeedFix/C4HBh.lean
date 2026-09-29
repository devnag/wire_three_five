import Proof.Wire_3_5.Primitive.SeedFix.C4HBg
import Proof.Wire_3_5.Primitive.SeedFix.C4HfO

/-! # C4HB, part 8: the call's data meets the printer's data facts (`hashData_ok`)

`filt:soft`, P3:2253-2290. **`hashData_ok`**: at a THR call's HASH stage the data `hashDataOf`
satisfies C4HB's `DataOk`: the moment count `t = listT … ≥ 1`; the HASH tape's rows `hashFsOf` are PA's `hashBatch`,
`N²·nE` of them; every population gate is a pool gate `oOff + i < |thrPool|` (`thrPool_getD_occ`).

Paper quantity of the main type: the HASH call's printed-objective data. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.RepairRepresentation

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
  (alg : DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))

/-- **The HASH call's data meets the printer's data facts.** -/
theorem hashData_ok : DataOk (hashDataOf alg I hs Cs carriers) where
  ht := C4Hf.hash_t_pos alg I hs Cs carriers
  hF := by
    rw [C4Hf.hD_N, C4Hf.hD_nE, C4Hf.hD_Fs]
    unfold hashFsOf PrimAsm.Batch.hashBatch
    simp
  hG := by
    intro pop hp gi hgi
    rw [C4Hf.hD_G]
    rw [C4Hf.hD_pops] at hp
    unfold hashPopsOf at hp
    simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_finRange, true_and,
      List.not_mem_nil, or_false] at hp
    obtain ⟨gi', pi, d, sgn, _, rfl⟩ := hp
    unfold hashGis at hgi
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hgi
    rw [List.eq_of_mem_replicate hi]
    exact (C4Hf.thrPool_getD_occ (I.starParams n hs) Cs carriers i).2.le

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4HB
