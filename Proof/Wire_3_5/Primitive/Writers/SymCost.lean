import Proof.Wire_3_5.Primitive.Writers.SymClass
import Proof.Wire_3_5.Primitive.Writers.ShellSInst

/-! # SYM leaf, part 3: the SYM shell's budget

The SYM shell v2's budget `2·shellCostG + 2` (`ShellS.shell_runSym`'s `hB`) at the SYM dimension stage's cost `c₂`
(`2·NumsXS.numsStageCostS + 2`) and the SYM data stage's cost `cc` (`Data.coreCost`). `shellCostG` reads `c₂` once,
additively, so the budget is THR v2's `costT` (at `c_r = K_L = 0`) plus `2c₂`, and `ShellT.costT_le` bounds it:

* `costS`, **`costS_le`**: `costS … ≤ K_c(|w|+n+cc+2)^E + K_c(2^m+1)^E + b·(2nU + 2R + 10) + 2c₂`.

Paper quantity of the main type: the SYM writer's running time (prim:runtime P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

/-- **The SYM shell's budget** at the dimension stage's cost `c₂`, the unit budget capped at `R`. -/
def costS (D C D2 C2 Dv Cv DL CL : ℕ) (lw n cc c2 nU m : ℕ) : ℕ :=
  2 * shellCostG (List.replicate lw false) n D C D2 C2 cc Dv Cv c2 m DL CL (min nU (UnaryCalc.value D C (2 ^ m))) + 2

theorem costS_le_T (D C D2 C2 Dv Cv DL CL : ℕ) (lw n cc c2 nU m : ℕ) :
    costS D C D2 C2 Dv Cv DL CL lw n cc c2 nU m ≤ costT D C D2 C2 Dv Cv 0 DL CL 0 lw n cc nU m + 2 * c2 := by
  unfold costS costT shellCostG bootXCostG
  omega

/-- **The SYM budget's bound.** -/
theorem costS_le (D C D2 C2 Dv Cv DL CL : ℕ) (lw n cc c2 nU m : ℕ) :
    costS D C D2 C2 Dv Cv DL CL lw n cc c2 nU m ≤
      KcT D C D2 C2 Dv Cv 0 DL CL 0 * (lw + n + cc + 2) ^ EcT D D2 Dv DL +
      KcT D C D2 C2 Dv Cv 0 DL CL 0 * (2 ^ m + 1) ^ EcT D D2 Dv DL +
      UnaryCalc.value DL CL (2 ^ m) * (2 * nU + 2 * UnaryCalc.value D C (2 ^ m) + 10) + 2 * c2 := by
  have h1 := costS_le_T D C D2 C2 Dv Cv DL CL lw n cc c2 nU m
  have h2 := costT_le D C D2 C2 Dv Cv 0 DL CL 0 lw n cc nU m
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
