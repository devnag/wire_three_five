import Proof.Wire_3_5.Primitive.SeedFix.SWt4Base

/-! # T3 SWt, part 5: **`swT x hx l : SWParts.SWtT l`**

**`tRun`**: at a SYM request, from the core's blank entry at the capacity `K_t·X^{D_t}`: the SYM front
(`front_runA`), every register cleared (the `clearL`), the four slots (`tops_run`, the words by `swt_word`); within
`C_t·X^{D_t'}` steps, every head and register `0`, the residue the front's. **`swT`** packages it as X6's
`GuardedWordsMJ` at the SYM guard.

Paper quantity of the main type: the SYM call's framed top tables (`symWords`, kind `1`; P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SWt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.NumsA NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

section Gate
variable (x : ℕ) (hx : DataDock.DT + 7 ≤ x) (l : Literals)

theorem scan_len {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) :
    2 * natBitLength C.bottomCount + 2 * (List.ofFn C.top).length + 2 ≤ (FinalPass.Out.DataW.scanWord C).length := by
  have hnw : (natWord C.bottomCount).length = 2 * natBitLength C.bottomCount + 1 := by
    have : natWord C.bottomCount = List.replicate (natBitLength C.bottomCount) true ++
      false :: WilliamsPublishedForm.fixedWidthNatBits (natBitLength C.bottomCount) C.bottomCount := rfl
    rw [this]; simp [WilliamsPublishedForm.fixedWidthNatBits]; omega
  unfold FinalPass.Out.DataW.scanWord
  simp only [List.length_append, hnw, frame_len']
  omega

end Gate

end NearCubicWires.WireExponent3_5.PrimT.SWt
