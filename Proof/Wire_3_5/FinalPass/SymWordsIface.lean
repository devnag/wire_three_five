import Proof.Wire_3_5.FinalPass.Asm2

/-! # The SYM words writer's interface (P3:1508-1520, 3046-3048, 3170-3178)

The core half (S5Core) writes the front's SYM slots `16 … 32` of `frontWordsW2`: `symWords` (16 words: the
circuits' gate tables, top tables, the list seeds' flat tables, the stage-5 templates) and the unary list of `symNums` (S3Words). Their writer is a word machine on its own layout, docked into S5Core by focus:

* **`SymWordsW l`**: the layout (`ns`, `nr`, the input stream `sIn`, the 17 output streams `sOut`), the program `P`,
  the coefficient `C F` (after the gate) and the degree `D` (before it), and the run at every SYM request of every
  call family: from the framed input `fpIn r` (every other stream blank, heads and registers `0`, cell `false`),
  within `C F·(|fpIn r|+1)^D` steps at that register capacity, the outputs are `frontWordsW2 r` at slots
  `16 + k`, the input is kept, every other stream is `0^ℓ` (`ℓ` within the capacity), heads and registers `0`;
* **`SymWordsW.step`**: the run as a machine `Step` (`WExec.exec`, `Exec.step`), S5Core's docking form.

Paper quantity of the main type: the SYM evaluator's call words (`symWords`, `symNums`, P3:1508-1520, 3170-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan

theorem sw0_nw : Sw0.nw = 16 := rfl

/-- The SYM slot `16 + k`. -/
def symSlot (k : Fin 17) : Fin (17 + Sw0.nw) := ⟨16 + k.val, by rw [sw0_nw]; omega⟩

end NearCubicWires.WireExponent3_5.FinalPass.Finish
