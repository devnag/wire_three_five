import Lean
import Proof.Wire_3_5.UnionMachine.NumsN1
import Proof.Wire_3_5.UnionMachine.NumsA7
import Proof.Wire_3_5.FinalPass.SWParts
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsN2Base


noncomputable section
set_option maxRecDepth 4096


/-! # SWn, part 2: the slot, its eighteen numbers, and `tabLen` in registers

The SYM slot `32` of `frontWordsW2` is the unary list of the call numbers `S3.symNums k` (`k = symCallOf …`): the tuple
size `a`, `|FlatSeed|`, then per circuit `j`: `|G_j|`, `tabH G_j`, `tabLen k j = t·(1 + (J+1)(2|G_j|+1)) + 1` (the walk
length `t`, the base list's `J`), the template's length. Here:

* **`swn_word`** (the slot is `unaryList (ofFn (symNums k))`), **`ofFn_symNums`** (the eighteen numbers in order);
* **`tabLen_regs`** (`tabLen k j` in register form), `R7`, `tabLenW` (the flat table's length from registers `L`, `J`,
  `t`), **`tabLen_run`**.

Paper quantities of the main type: the SYM call numbers (P3:3170-3178, list:flatten P3:1508-1520). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (mulStep mulStep_spec mulCost mulCost_le)

section Link
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The numbers' slot**: `SWnT`'s word is `unaryList (ofFn (symNums k))`. -/
theorem swn_word {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    FinalPass.SWParts.swWs l 16 1 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ 0 =
      Data.unaryList (List.ofFn (PrimT.S3.symNums
        (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers))) := by
  have hv : (symSlot ⟨16 + (0 : Fin 1).val, by omega⟩).val = 32 := rfl
  simp only [FinalPass.SWParts.swWs, FinalPass.Seams.frontWordsW2, FinalPass.Seams.frontWordsOfW2, dif_pos hs]
  have e3 : FinalPass.Finish.Sw0.nw = 16 := sw0_nw
  split_ifs with h1 h2 h3
  · omega
  · omega
  · omega
  · rfl

end Link

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
