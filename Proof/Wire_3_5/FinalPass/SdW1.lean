import Proof.Wire_3_5.FinalPass.SdB1
import Proof.Wire_3_5.FinalPass.TabBd2

/-! # S4 (the seeds phase), part 47: the tables writer's budget, polynomial (P3:3170-3178)

The tables writer's budget `2·shellCostG (reqT …) … + 2` (`tab_writer`'s `Bud`) is within the v2 shell budget
`costT` (its dimension stage's `c2Of` is below `costT`'s `numsStageCostT`, `c2Of_le`; the loop's budget is `nU` since
`nU + 1 ≤ R`), so within `ShellT.costT_le`'s polynomial (**`bud_le`**): in the request side `|w| + n + cc` and the
dimension `2^m`.

Paper quantity of the main type: the seeds phase's tables writer's running time (the filter seeds' tables, P3:2036-2101,
3170-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires.BlockPlatform

theorem c2Of_le (cr n : ℕ) :
    c2Of cr n ≤ 2 * NumsXT.numsStageCostT n cr 0 (UnaryCalc.value 1 (cr + 18) n) + 2 := by
  unfold c2Of NumsX.numsStageCost NumsXT.numsStageCostT NumsXT.numsCostT
  omega

theorem bud_le (w : List Bool) (n D C cc cr m DL CL nU : ℕ) (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ m)) :
    2 * shellCostG w n D C 1 64 cc 1 (cr + 18) (c2Of cr n) m DL CL nU + 2 ≤
      KcT D C 1 64 1 (cr + 18) cr DL CL 0 * (w.length + n + cc + 2) ^ EcT D 1 1 DL +
      KcT D C 1 64 1 (cr + 18) cr DL CL 0 * (2 ^ m + 1) ^ EcT D 1 1 DL +
      UnaryCalc.value DL CL (2 ^ m) * (2 * nU + 2 * UnaryCalc.value D C (2 ^ m) + 10) := by
  have h := costT_le D C 1 64 1 (cr + 18) cr DL CL 0 w.length n cc nU m
  have hmin : min nU (UnaryCalc.value D C (2 ^ m)) = nU := min_eq_left (by omega)
  have hc2 := c2Of_le cr n
  unfold costT at h
  rw [hmin, ← shellCostG_len w] at h
  have mono : shellCostG w n D C 1 64 cc 1 (cr + 18) (c2Of cr n) m DL CL nU ≤
      shellCostG w n D C 1 64 cc 1 (cr + 18) (2 * NumsXT.numsStageCostT n cr 0 (UnaryCalc.value 1 (cr + 18) n) + 2)
        m DL CL nU := by
    unfold shellCostG bootXCostG
    omega
  omega

end NearCubicWires.WireExponent3_5.FinalPass.TabW
