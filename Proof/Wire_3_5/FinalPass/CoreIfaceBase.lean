import Proof.Wire_3_5.FinalPass.SymWordsIface

/-! # The core half's word writers: interfaces (P3:3044-3048, 3170-3181)

The core half (S5Core) writes the front's words that the THR half does not: S4's 8 words (`s4Core2`, slots `0 … 7`
of `frontWordsW2`), the SYM evaluator's words (slots `16 … 32`, `SymWordsW`) and the two numbers S4 starts from
(`Num = 0`, `Den = fpDen` in `W`-bit binary, `W = Sd.R.Tf`). Each writer is a word machine on its own layout, docked
into S5Core by focus (the form of `SymWordsW`):

* **`CoreWordsW l m ws`**: the layout (`ns`, `nr`, the input stream `sIn`, the `m` output streams `sOut`), the
  program `P`, the coefficient `C F` (after the gate) and the degree `D` (before it), and the run at EVERY request of
  every call family: from the framed input `fpIn r` (every other stream blank, heads and registers `0`, cell `false`),
  within `C F·(|fpIn r|+1)^D` steps at that register capacity, the outputs are `ws r k`, the input is kept, every other
  stream is `0^ℓ` (`ℓ` within the capacity), heads and registers `0`; **`CoreWordsW.step`** (the machine form);
* **`S4WordsWA l`** (slots `0 … 3`: the coset offset, the sampled pairs, the two carriers' mask tables),
  **`S4WordsWB l`** (slots `4 … 7`: the field words `τ`, the modulus, the majority threshold, the small numbers
  `s4Small2`), **`NumsW l`** (`frame (binary W 0)`, `frame (binary W fpDen)`, `W = Sd.R.Tf`).

Paper quantities of the main types: S4's own words (`s4Core2`: the offset, the samples, the carriers' tables, the
filter's field words, the threshold, the call's small numbers; P3:3170-3181) and the printed denominator `fpDen` at
the width `W` (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- S4's slot `k` (`k < 4`). -/
def s4SlotA (k : Fin 4) : Fin (17 + Sw0.nw) := ⟨k.val, by rw [sw0_nw]; omega⟩

/-- S4's slot `4 + k`. -/
def s4SlotB (k : Fin 4) : Fin (17 + Sw0.nw) := ⟨4 + k.val, by rw [sw0_nw]; omega⟩

end NearCubicWires.WireExponent3_5.FinalPass.Finish
