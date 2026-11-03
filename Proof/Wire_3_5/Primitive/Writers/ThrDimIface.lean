import Lean
import Proof.Wire_3_5.Primitive.Writers.ShellT2
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
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup


noncomputable section
set_option maxRecDepth 4096


/-! # THRTAIL: the THR dimension stage's interface `ThrDimStage` (types only)

P3:3094-3107 (the THR load `Ψ_T = C_D((k+L)²·d_T + k + L²)`, `d_T = C_D(√(B_T·L) + L²)`) and THRU4's `meas_le` (the
unit's measure within `2^{K_m·Ψ_T}`): the THR writer shell (`ShellT.shellMGH4`, `shell_runH4`) needs a dimension stage
`M2` (ShellT's `DimOK`: from `frame w` and `1^W`, the CapReader source of `2^{m_T}`) whose dimension covers the unit
budget, `m_T ≥ mOfT K_L P + K_f·Ψ_T(P)` (so `2^{m_T}` covers `2^{K_m·Ψ_T}`, the loop's `thrTOT`, the capacity, the
per-unit budget), and stays in the preprocessing class, `m_T ≤ mOfT K_L P + 8·K_f·Ψ_T(P)` (`Ψ_T ≤ Ψ = psiOf`). `Ψ_T` is
read at the star parameters `P`: `k = P.k`, `L = ⌈log₂(n+2)⌉`, the THR cap `B_T = rowBCap (gateCap l) .thr P.r s_p n`.

* `bT`, `psiT`; **`ThrDimStage l F K_L K_f D_n D_c`** (the machine, its dimension, cost and fill need, `dimOK`, the two
  dimension bounds, the need and cost within `(n+1)^{D_n}`, `(W+n+1)^{D_c}`, the exponents `D_n`, `D_c` fixed by `l`).

PA2 builds the instance (T-A: `NumsXT2`, the twin of SYM's `NumsXS`: star numbers, sparse count, `CapNum` at `.thr`,
`k' = r·natBitLength(n/r+1) ∈ [k, 2k]`, `⌈√(B_T·L)⌉`, the products); T3 builds T-B against this type.

Paper quantity of the main type: the THR writer's dimension `2^{m_T}` with `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrDim
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.LocalBitMultitape

/-- The THR cap at the star parameters (`B_T = rowBCap C .thr r s_p n`). -/
noncomputable def bT (l : Literals) (P : Shared.StarParams) : ℕ :=
  Ledger.rowBCap (gateCap l) .thr P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n) P.n

/-- **The THR load at the star parameters**: `Ψ_T = loadThr C_D k L B_T`. -/
noncomputable def psiT (l : Literals) (CD : ℕ) (P : Shared.StarParams) : ℕ :=
  loadThr CD P.k (Nat.clog 2 (P.n + 2)) (bT l P)

/-- **The THR writer's dimension stage** at the gate `F` (its `c_r`, `C_D`), the dimension's `L²` coefficient `K_L`,
the load's multiplier `K_f`, and the fill need's / cost's exponents `D_n`, `D_c` (fixed by `l`). -/
structure ThrDimStage (l : Literals) (F : GateFree l) (KL Kf Dn Dc : ℕ) where
  /-- the machine's control states -/
  s2 : ℕ
  /-- the dimension stage (on `NUn` tapes, docked by ShellT's `q2`) -/
  M2 : Machine ShellX.NUn s2
  /-- the dimension `m_T` -/
  mT : Shared.StarParams → ℕ
  /-- the stage's steps at the fill count `W` -/
  c2 : ℕ → Shared.StarParams → ℕ
  /-- the fill count the stage needs -/
  need : Shared.StarParams → ℕ
  /-- **the stage leaves the source of `2^{m_T}`** (ShellT's `DimOK`) from any fill `W ≥ need P` -/
  dimOK : ∀ (x D D2 Dv DL : ℕ) (P : Shared.StarParams), P.r = Ledger.rowBr F.cr P.n →
    ∀ (sfx w : List Bool), w = RepairRepresentation.natWord P.n ++ sfx → ∀ W : ℕ, need P ≤ W →
      ShellT.DimOK x D D2 Dv DL M2 (c2 W P) (mT P) w W
  /-- **the dimension covers the unit budget** -/
  m_ge : ∀ P : Shared.StarParams, PrimThrW.Shell2.mOfT KL P + Kf * psiT l F.CD P ≤ mT P
  /-- **the dimension stays in the preprocessing class** -/
  m_le : ∀ P : Shared.StarParams, mT P ≤ PrimThrW.Shell2.mOfT KL P + 8 * Kf * psiT l F.CD P
  /-- the fill need's coefficient (after `F`) -/
  Kn : ℕ
  need_le : ∀ P : Shared.StarParams, P.r = Ledger.rowBr F.cr P.n → need P ≤ Kn * (P.n + 1) ^ Dn
  /-- the cost's coefficient (after `F`) -/
  Kc : ℕ
  c2_le : ∀ (W : ℕ) (P : Shared.StarParams), c2 W P ≤ Kc * (W + P.n + 1) ^ Dc

end NearCubicWires.WireExponent3_5.PrimAsm.ThrDim

end
