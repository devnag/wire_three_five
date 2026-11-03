import Lean
import Proof.Wire_3_5.Primitive.Writers.NumsXT2Run
import Proof.Wire_3_5.Primitive.Writers.ThrDimIface
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ShellT2
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit
import Proof.Wire_3_5.Primitive.Writers.SymNeedBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4V
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase


noncomputable section
set_option maxRecDepth 4096


/-! # THRTAIL T-A1: the THR dimension stage at the gate, and `ThrDimStage` from four bounds

`NumsXT2Run`'s stage at the gate constants (`ζ`, `C_δ`, `C` of `gate0 l F`, the gate's `c_r`, `C_D`), with the three
quantities T-A2 bounds stated explicitly:

* **`mTG l F K_L K_f P`** `= mOfT K_L P + T`, `T = K_f·C_D·((k' + L)²·C_D·(⌈√(B_T·L)⌉ + 1 + L²) + k' + L²)`,
  `k' = r·natBitLength(n/r + 1)`, `B_T = bT l P`, `L = ⌈log₂(n+2)⌉`, `C_D = F.CD`;
* **`c2G l F K_L K_f W P`** `= 2·numsStageCostT2 W P … + 2` (the stage's steps at the fill count `W`);
* **`needG l F K_L K_f P`** (the fill count the stage needs: the sum of `TNeed2`'s terms, `CapNeed` through
  `capNeed_ofT`'s one bound `capNT`);
* **`dimOK_G`** (`ThrDimStage.dimOK` at these), and **`thrDimStage_of`**: `ThrDimStage l F K_L K_f D_n D_c` from
  T-A2's `m_ge`, `m_le`, `need_le`, `c2_le` at exactly these definitions.

Paper quantity of the main type: the THR writer's dimension `2^(m_T)`, `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrDim
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.LocalBitMultitape

section Gate
variable (l : Literals) (F : GateFree l) (KL Kf : ℕ)

/-- `capNeed_ofT`'s one bound for CapNum's `.thr` capacity conditions at `n`. -/
noncomputable def capNT (n : ℕ) : ℕ :=
  2 ^ 40 * (CallIndexR.capK F.cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
    CapNum.cMain (gateCap l) .thr

/-- **The stage's dimension** `m_T` at the gate. -/
noncomputable def mTG (P : Shared.StarParams) : ℕ :=
  NumsXT2.mT2 KL P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf

/-- **The stage's steps** at the fill count `W`. -/
noncomputable def c2G (W : ℕ) (P : Shared.StarParams) : ℕ :=
  2 * NumsXT2.numsStageCostT2 W P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf KL F.cr + 2

/-- **The fill count the stage needs.** -/
noncomputable def needG (P : Shared.StarParams) : ℕ :=
  (2 * P.n + F.cr + 16 + KL * (P.n + 2) ^ 2) +
    SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq P.n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n - 1) +
    capNT l F P.n + Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n +
    NumsXT2.xNeedT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) +
    NumsXT2.tNeedT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf +
    (2 * mTG l F KL Kf P + 3)

/-- **The stage** at the gate. -/
noncomputable def M2G := NumsXT2.numsMT2 KL F.cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) F.CD Kf

/-- The stage's capacity needs from the fill need. -/
theorem tneed_of (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr F.cr P.n) (W : ℕ) (h : needG l F KL Kf P ≤ W) :
    NumsXT2.TNeed2 W P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf KL F.cr := by
  unfold needG capNT mTG at h
  have hc := PrimT.TS4.capNeed_ofT l F.cr P.n (2 * W + 2) (by omega)
  rw [← hrP] at hc
  exact ⟨by omega, by omega, hc, by omega, by omega, by omega, by omega⟩

/-- **`ThrDimStage.dimOK` at the gate.** -/
theorem dimOK_G : ∀ (x D D2 Dv DL : ℕ) (P : Shared.StarParams), P.r = Ledger.rowBr F.cr P.n →
    ∀ (sfx w : List Bool), w = RepairRepresentation.natWord P.n ++ sfx → ∀ W : ℕ, needG l F KL Kf P ≤ W →
      ShellT.DimOK x D D2 Dv DL (M2G l F KL Kf) (c2G l F KL Kf W P) (mTG l F KL Kf P) w W :=
  fun _ _ _ _ _ P hrP sfx w hw W hW =>
    NumsXT2.dimOK_numsT2 KL F.cr P hrP (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf sfx w hw W
      (tneed_of l F KL Kf P hrP W hW)

/-- **`ThrDimStage` from T-A1 and T-A2's four bounds** at exactly `mTG`, `needG`, `c2G`. -/
noncomputable def thrDimStage_of (Dn Dc : ℕ)
    (m_ge : ∀ P : Shared.StarParams, PrimThrW.Shell2.mOfT KL P + Kf * psiT l F.CD P ≤ mTG l F KL Kf P)
    (m_le : ∀ P : Shared.StarParams, mTG l F KL Kf P ≤ PrimThrW.Shell2.mOfT KL P + 8 * Kf * psiT l F.CD P)
    (Kn : ℕ) (need_le : ∀ P : Shared.StarParams, P.r = Ledger.rowBr F.cr P.n → needG l F KL Kf P ≤ Kn * (P.n + 1) ^ Dn)
    (Kc : ℕ) (c2_le : ∀ (W : ℕ) (P : Shared.StarParams), c2G l F KL Kf W P ≤ Kc * (W + P.n + 1) ^ Dc) :
    ThrDimStage l F KL Kf Dn Dc where
  s2 := _
  M2 := M2G l F KL Kf
  mT := mTG l F KL Kf
  c2 := c2G l F KL Kf
  need := needG l F KL Kf
  dimOK := dimOK_G l F KL Kf
  m_ge := m_ge
  m_le := m_le
  Kn := Kn
  need_le := need_le
  Kc := Kc
  c2_le := c2_le

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrDim

end
