import Proof.Wire_3_5.Primitive.SeedFix.SWt2
import Proof.Wire_3_5.FinalPass.SymFront4
import Proof.Wire_3_5.FinalPass.SWParts

/-! # SWt, part 3: the four slots and their word link

On the SYM front bank (`x ≥ DT + 7`): the scan tapes `sS j` (FrontOut's `scan`, blank past the tuple), the output
streams `sO j` (four blank streams past the data region), the registers `RT`, **`tW`** (every register cleared, then
`topW` at each slot), **`swt_word`** (SWtT's word `j` is `frame (topJ k j)`), **`tops_run`** (the four slots from a
bank with the scan words on `sS j`, `sO j` blank: the bank with `sO j := frame (topJ k j)`).

Paper quantity of the main types: the SYM call's framed top tables (`symWords`, kind `1`; P3:3170-3178). -/

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

/-- The registers. -/
def RT : Fin 8 ↪ Fin LNR := ⟨fun i => ⟨i.val, by have := i.isLt; show i.val < 512; omega⟩, fun i j h => by
  have := congrArg Fin.val h; exact Fin.ext this⟩

/-- Every register. -/
def allR : List (Fin LNR) := List.finRange LNR

section Gate
variable (x : ℕ) (hx : DataDock.DT + 7 ≤ x)

theorem hx3 (hx : DataDock.DT + 7 ≤ x) : DataDock.DT + 3 ≤ x := by omega

/-- The scan tapes. -/
def sS (j : Fin 4) : Fin (LNS x + 1) :=
  tmapA x (hx3 x hx) (DataDock.iOf (Data.sSym j (PrimT.SymTab.scanSl 0)))

theorem sS_val (j : Fin 4) : (sS x hx j).val = 1870 + 1789 * j.val := by
  unfold sS
  rw [tmapA_val x (hx3 x hx) _ (by intro e; have := congrArg Fin.val e; revert this; fin_cases j <;> decide)]
  fin_cases j <;> rfl

/-- The output streams: four blank streams past the data region. -/
def sO (j : Fin 4) : Fin (LNS x + 1) := sT x ⟨DataDock.DT + 3 + j.val, by have := j.isLt; omega⟩

theorem sO_val (j : Fin 4) : (sO x hx j).val = 161 + (DataDock.DT + 3 + j.val) := rfl

theorem DT_ge : 1870 + 1789 * 3 < 161 + DataDock.DT := by decide

theorem sO_inj : Function.Injective (sO x hx) := fun i j h => by
  have := congrArg Fin.val h; rw [sO_val, sO_val] at this; exact Fin.ext (by omega)

/-- **The top tables' output streams.** -/
def sOutT : Fin 4 ↪ Fin (LNS x + 1) := ⟨sO x hx, sO_inj x hx⟩

theorem sS_ne_sO (i j : Fin 4) : sS x hx i ≠ sO x hx j := fun e => by
  have := congrArg Fin.val e; rw [sS_val, sO_val] at this; have := DT_ge; have := i.isLt; omega

theorem sO_ne_sIn (j : Fin 4) : sO x hx j ≠ sIn x := fun e => by
  have := congrArg Fin.val e; rw [sO_val] at this; simp [NumsPh2.sIn_val] at this; omega

/-- **The top tables' program** after the front. -/
def tW : WM (LNS x) LNR :=
  .seq (NumsC.clearL allR) (.seq (topW (sS x hx 0) (sO x hx 0) RT) (.seq (topW (sS x hx 1) (sO x hx 1) RT)
    (.seq (topW (sS x hx 2) (sO x hx 2) RT) (topW (sS x hx 3) (sO x hx 3) RT))))

end Gate

end NearCubicWires.WireExponent3_5.PrimT.SWt
