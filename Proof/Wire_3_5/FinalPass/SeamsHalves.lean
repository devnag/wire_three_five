import Lean
import Proof.Wire_3_5.FinalPass.SeamsBank2Base
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.FinalPass.SeamsProg3Base


noncomputable section
set_option maxRecDepth 4096


/-! # The portable tail's two targets (C1b): the core half and the out machine, generic in the bank

The finalpass assembly (`Assembly.finalPass_of3`, v3 seams) consumes the core half at S4's bank (next to the THR half,
`ThrHalfGen2`) and the out machine at the seeds phase's layout (`SeedsProg4`, from BridgeT). Both producers are
portable, so their targets are stated generic in the layout:

* **`CoreHalfGen2 Sw mT mC`** (S5Core's target): `ThrHalfGen2`'s twin for the core half, `S5CoreB3` at every bank with
  rooms `mT l`, `mC l`. The producer fixes `mCore : Literals → ℕ` and proves `∀ mT, CoreHalfGen2 Sw mT mCore` at
  `Sw := Seams.SymPtEval2.toWords PrimT.S3.symPtEval`.
* **`OutGen mX`** (X6's target): `OutMachine2` on every layout `t` with output `o`, numbers `tN`, `tD` and an
  `mX`-tape room `e` inside the scratch set `sc`, off `o`, `tN`, `tD`. The producer fixes `mOut : ℕ` and proves
  `OutGen mOut`.

Paper quantities of the main types: the front's words (`frontWordsW2`, P3:3170-3181) and the printed rational
`ratWord (Num/Den)` (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam NearCubicWires.WireExponent3_5.Split

/-- **The core half's target, generic in the bank**, rooms `mT l`, `mC l`, at every call family. -/
abbrev CoreHalfGen2 (Sw : SymWords) (mT mC : Literals → ℕ) : Type :=
  ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    HalfGen2 (fun L : S5Lay Sw.nw => S5CoreB3 l F kclk coef A a ha Sw L) (mT l) (mC l)

/-- **The out machine's target, generic in the layout**: an `mX`-tape room inside the blank scratch set, off the
output and number tapes. -/
abbrev OutGen (mX : ℕ) : Type :=
  ∀ (t : ℕ) (o tN tD : Fin t) (sc : Fin t → Bool) (e : Fin mX ↪ Fin t), (∀ i, sc (e i) = true) →
    (∀ i, e i ≠ o ∧ e i ≠ tN ∧ e i ≠ tD) → o ≠ tN → o ≠ tD → tN ≠ tD → OutMachine2 t o tN tD sc

end NearCubicWires.WireExponent3_5.FinalPass.Bank

end
