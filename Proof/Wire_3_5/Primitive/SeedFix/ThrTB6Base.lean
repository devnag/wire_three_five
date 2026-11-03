import Proof.Wire_3_5.Primitive.SeedFix.ThrTB5
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase

/-! # T3 THRTAIL T-B, part 6: the THR writer's run at a call

The THR writer `thrM` = the v4 shell `shellMGH4` over the v4 data stage `S`, the unit machine `U` (THRU4) and
T-A's dimension stage `thrDimStageG l F K_L K_f` (`K_L = kLT l f_e D₀`, `K_f = D₀ + 1`), the scrub capacity
`(dSh D₀, cSh D₀ C₀ C_L)`, the data width `(dT2 l D₀, cT2 l F C₀)`, the fill `(D_nG, K_n)`, the loop `(1, C_L)`.
**`thr_run`**: at every THR call, from `frame thrCallW`, within `128·K²·Y^E·Y^E` (`Y = 2^{m_T} + 1`, `costG_le`),
the output is the THR tape (`shell_runH4`; the unit's `UnitOK` from `U.ok` at `cap = need(meas) + b`;
`ThrTail.thr_loop_tape` at `b = C_L·Y ≥ thrTOT`).

* `thrM`, `eT`, `kTB`, `budT`; **`thr_run`**.

Paper quantity of the main type: the THR tape `thrTape` (C4's `BAT` word, P3:3011-3016) written within
`2^{O(m_T)}` steps. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.RepairOrdinary

section Writer
variable (l : Literals) (fe D0 C0 kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
 
 

/-- The monomial bound at `Y ≥ n + 1`. -/
theorem mono_Y {X c d Y E n : ℕ} (hX : X ≤ c * (n + 1) ^ d) (hn : n + 1 ≤ Y) (hd : d ≤ E) : X ≤ c * Y ^ E :=
  hX.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hn d).trans (Nat.pow_le_pow_right (by omega) hd)))

/-- The data stage's cost, arithmetic: `C_c(3V + n + 1)^{D_c} ≤ K·Y^E`. -/
theorem cc_arith (cost Cc Dc V n Y D0 C0 c2 d2 E K : ℕ) (hc : cost ≤ Cc * (V + n + V + V + 1) ^ Dc)
    (hCc : Cc ≤ C0) (hDc : Dc ≤ D0) (hV : V ≤ c2 * Y ^ d2) (hnY : n + 1 ≤ Y ^ d2) (hY : 1 ≤ Y) (hE : d2 * D0 ≤ E)
    (hK : C0 * (3 * c2 + 1) ^ D0 ≤ K) : cost ≤ K * Y ^ E := by
  obtain ⟨Z, hZ⟩ : ∃ x, x = Y ^ d2 := ⟨_, rfl⟩
  rw [← hZ] at hV hnY
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_pow _ _ hY
  have hb : V + n + V + V + 1 ≤ (3 * c2 + 1) * Z := by
    have e : (3 * c2 + 1) * Z = 3 * (c2 * Z) + Z := by ring
    omega
  have hb1 : 1 ≤ (3 * c2 + 1) * Z := by nlinarith
  have hp : (V + n + V + V + 1) ^ Dc ≤ (3 * c2 + 1) ^ D0 * Y ^ (d2 * D0) := by
    calc (V + n + V + V + 1) ^ Dc ≤ ((3 * c2 + 1) * Z) ^ Dc := Nat.pow_le_pow_left hb _
      _ ≤ ((3 * c2 + 1) * Z) ^ D0 := Nat.pow_le_pow_right hb1 hDc
      _ = (3 * c2 + 1) ^ D0 * Y ^ (d2 * D0) := by rw [mul_pow, hZ, ← pow_mul]
  calc cost ≤ Cc * (V + n + V + V + 1) ^ Dc := hc
    _ ≤ C0 * ((3 * c2 + 1) ^ D0 * Y ^ (d2 * D0)) := Nat.mul_le_mul hCc hp
    _ = C0 * (3 * c2 + 1) ^ D0 * Y ^ (d2 * D0) := by ring
    _ ≤ K * Y ^ E := Nat.mul_le_mul hK (Nat.pow_le_pow_right hY hE)

end Writer

section Dim

end Dim

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
