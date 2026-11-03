import Lean
import Proof.Wire_3_5.Primitive.SeedFix.SWt2
import Proof.Wire_3_5.FinalPass.SymFront4Base
import Proof.Wire_3_5.FinalPass.SWParts
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.SWt3Base


noncomputable section
set_option maxRecDepth 4096


/-! # T3 SWt, part 3: the four slots and their word link

On the SYM front bank (`x ≥ DT + 7`): the scan tapes `sS j` (FrontOut's `scan`, blank past the tuple), the output
streams `sO j` (four blank streams past the data region), the registers `RT`, **`tW`** (every register cleared, then
`topW` at each slot), **`swt_word`** (SWtT's word `j` is `frame (topJ k j)`), **`tops_run`** (the four slots from a
bank with the scan words on `sS j`, `sO j` blank: the bank with `sO j := frame (topJ k j)`).

Paper quantity of the main types: the SYM call's framed top tables (the `symWords`, kind `1`; P3:3170-3178). -/

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
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)

section Link
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The top tables' slots**: word `j` of `SWtT` is `frame (topJ k j)`. -/
theorem swt_word {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (j : Fin 4) :
    FinalPass.SWParts.swWs l 4 4 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ j =
      frame (PrimT.S3.topJ (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) j) := by
  have hv : (symSlot ⟨4 + j.val, by omega⟩).val = 16 + (4 + j.val) := by simp [symSlot]
  have hj := j.isLt
  simp only [FinalPass.SWParts.swWs, FinalPass.Seams.frontWordsW2, FinalPass.Seams.frontWordsOfW2, dif_pos hs]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · have e2 : (⟨(symSlot ⟨4 + j.val, by omega⟩).val - 16, h3⟩ : Fin 16) = PrimT.S3.wIdx 1 j :=
      Fin.ext (by show 16 + (4 + j.val) - 16 = 4 * 1 + j.val; omega)
    show PrimT.S3.symWords _ ⟨(symSlot ⟨4 + j.val, by omega⟩).val - 16, h3⟩ = _
    rw [e2, PrimT.S3.symWords_idx]
    rfl
  · exfalso
    have e3 : FinalPass.Finish.Sw0.nw = 16 := sw0_nw
    omega

end Link

section Gate

end Gate

end NearCubicWires.WireExponent3_5.PrimT.SWt

end
