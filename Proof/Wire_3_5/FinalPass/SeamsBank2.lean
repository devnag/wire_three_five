import Lean
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.FinalPass.SeamsS4
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.S5SeamB2
import Proof.Wire_3_5.FinalPass.SeamsBank2Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4's bank, v2: the front halves' room as parameters

`Bank` fixes each half's room at `4096` tapes; the THR half docks W6 (`NumsPort4`), which needs
about `10197 + 4·(Ta − 1)` tapes, a number that depends on the decomposition algorithm and so on `l`. Here the rooms
are PARAMETERS (`mT`, `mC`, chosen at each `l`): the halves declare them, and BridgeT's layout takes
`nr ≥ base + mT + mC`.

* **`HalfRoom2 L mT mC`**: `L`'s THR / core scratch contain `mT` / `mC` named tapes;
* **`HalfGen2 P mT mC`**: a half generic in the bank at those rooms (its register-length need `K·(|fpIn|+1)^D`);
* **`ThrHalfGen2 Sw mT mC`**: the THR half's target at every call family, rooms `mT l`, `mC l`;
* **`BankLay2 Sw mT mC`**: S4's bank with `base + mT + mC ≤ L.nr`; **`BankLay2.lay`**, **`BankLay2.hroom`**.

Paper quantity of the main types: none beyond the machine model (the final pass's one machine, P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam NearCubicWires.WireExponent3_5.Split

/-- **The THR half's target, generic in the bank**, rooms `mT l`, `mC l`, at every call family. -/
abbrev ThrHalfGen2 (Sw : SymWords) (mT mC : Literals → ℕ) : Type :=
  ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    HalfGen2 (fun L : S5Lay Sw.nw => S5ThrB2 l F kclk coef A a ha Sw L) (mT l) (mC l)

end NearCubicWires.WireExponent3_5.FinalPass.Bank

end
