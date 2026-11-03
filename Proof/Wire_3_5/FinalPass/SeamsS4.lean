import Proof.Wire_3_5.FinalPass.SeamsProg2Base

/-! # S4's word-level seam: the seeds phase as one word program (plan: one WM program, one bridge)

S4 is built as ONE word program on its own layout and compiled once; the bank-level `SeedsProg2` follows
from it by a single bridge (BridgeT: compile, `wenc`, `WExec.exec`, the front's blank tapes read like `[]`). This
file fixes the bridge's input so that the bridge and the program can be built in parallel:

* **`SdLay`**: the layout: `ns` streams, `nr` registers, the front's word streams `wdS`, the numerator and
  denominator streams `sN`, `sD` (all distinct);
* **`SdEntry`**: the internal entry at a request: the front's words `frontWordsW` on `wdS`, `frame (binary W 0)` on
  `sN`, `frame (binary W fpDen)` on `sD`, every other stream empty, every head at `0`, every register `0`, the cell
  `false`;
* **`SeedsWM`** (BridgeT's input; S4's program type at the word level): the layout, the program, the register
  capacity `Kc·(|fpIn|+1)^{Dc}`, the costs `tab`, `pt`, `ov` with `SeedsProg2`'s bounds, and the run: from every
  `SdEntry` with `ptCount·vmax < 2^W`, within `seedsShape`, `sN` ends as `frame (binary W fpNum)`, `sD` unchanged,
  every head at `0` and every register `0` (a register's value is its tape's head in `wenc`, and NumDenOut asks for
  every head at `0`), `fpNum < 2^W`.

The program's own inner seams (per-point step, the center/sample loops, the seed loop) stay inside this program.
Paper quantities: the printed numerator `fpNum = Σ_c Σ_e Σ_ℓ M·Σ R̂` and denominator (P3:3044-3048), the seeds
phase's cost `|E|·tab + (|centers|·|E|·Q)·pt + ov`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **S4's word layout.** -/
structure SdLay where
  ns : ℕ
  nr : ℕ
  wdS : Fin (17 + Sw.nw) → Fin (ns + 1)
  sN : Fin (ns + 1)
  sD : Fin (ns + 1)
  wdInj : Function.Injective wdS
  nd : sN ≠ sD
  wdN : ∀ k, wdS k ≠ sN
  wdD : ∀ k, wdS k ≠ sD

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
