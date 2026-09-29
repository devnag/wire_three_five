import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface

/-! # for THR and C6: the THR writer shell's run, part 1: the boot over a `ThrDataStage`

THR's `PrimThrW.Shell.ThrShellRun` is ShellX's run with the SYM data stage replaced by
any `ThrData.ThrDataStage` and the unit machine by any machine meeting `UnitOK`. This file proves the boot half,
ShellX's own proofs with the data stage's `run` in place of `Data.data_step`:

* `st8T` (the data stage docked on `ShellD.dataSlots`), **`pre_stepT`** (the boot and data phase), `x0_stepT` (docked
  on ShellX's layout);
* the dimension stage as a parameter (v1 at `mOf`, v2 at `mOfT`): **`DimOK`** (a stage `M2` on ShellX's
  `q2` writing the CapReader source of `2^m`), `bootXMG`, `bootXCostG`, `dimOK_nums` (ShellX's stage meets it);
* **`bootX_stepG`** (ShellX's boot with any `DimOK` stage: the loop's entry data on the real layout, the data tape
  `Data.dataWord (ThrData.thrCounts Cs carriers)`, the counter `word b`, `b = CL(2^m+1)^DL`).

Paper quantity of the main type: the THR call's slice lengths `ThrData.thrCounts` on the writer's data tape
(lem:primitive P3:3068-3084) and the loop's dimension `n' = 2^(2·kh + L)` (P3:1188-1189, 3823-3824). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Shell (install_eq dockH_eq)

section Data

end Data

section Pre

end Pre

section Boot
variable {x D D2 Dv DL : ℕ}

/-- **A dimension stage** `M2` docked on ShellX's `q2`: from the request `frame w` and the fill `1^W`, within `c2`
steps, the CapReader source of `2^m` on its output, the request kept. -/
def DimOK (x D D2 Dv DL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) (c2 m : ℕ) (w : List Bool) (W : ℕ) : Prop :=
  ∀ B : Fin (STx x D D2 Dv DL) → List Bool, B (T0 x D D2 Dv DL) = frame w →
    B (TW x D D2 Dv DL) = List.replicate W true → (∀ k, B (nu k) = []) →
    ∃ tout : Fin NUn → List Bool,
      Step (RecoveryFocus.machine (q2 x D D2 Dv DL) M2) c2 HI B HI (install (q2 x D D2 Dv DL) B tout) ∧
      tout oN = NumsX.srcWord m ∧ tout iN = frame w

/-- **The THR boot with any dimension stage** (`PrimThrW.Shell.bootXMT` at `M2 = NumsX.numsM cr`). -/
noncomputable def bootXMG (S : ThrData.ThrDataStage) (x D D2 Dv DL C2 Cv CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (PrimThrW.Shell.MX0T S x D D2 Dv DL C2) (MX1 x D D2 Dv DL Cv))
      (RecoveryFocus.machine (q2 x D D2 Dv DL) M2)) (MX3 x D D2 Dv DL)) (MX4 x D D2 Dv DL CL)) (MX5 x D D2 Dv DL))
    (act6 x D D2 Dv DL).compile

/-- The boot's cost with the dimension stage's cost `c2` (`ShellX.bootXCost` at `c2 = 2·numsStageCost + 2`). -/
def bootXCostG (w : List Bool) (n D2 C2 cc Dv Cv c2 m DL CL : ℕ) : ℕ :=
  preCost w n 0 0 D2 C2 cc + 1 + PCPSerializerCapacity.Power.budget Dv Cv n + 1 + c2 + 1 + capCost m + 1 +
    PCPSerializerCapacity.Power.budget DL CL (2 ^ m) + 1 + (2 * UnaryCalc.value DL CL (2 ^ m) + 3) + 1 + 1

/-- ShellX's dimension stage meets `DimOK` at `mOf P`. -/
theorem dimOK_nums (cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (W : ℕ) (hW : 2 * P.n + cr + 16 ≤ W) :
    DimOK x D D2 Dv DL (NumsX.numsM cr) (2 * NumsX.numsStageCost P.n cr W + 2) (NumsX.mOf P) w W :=
  fun B h0 hct hb => x2_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) cr W P hrP sfx w hw hW B h0 hct hb

end Boot

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
