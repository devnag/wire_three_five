import Lean
import Proof.Wire_3_5.Primitive.Writers.NumsXT2Gate
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.ThrDimIface
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.UnionMachine.ThrDimMBase


noncomputable section
set_option maxRecDepth 4096


/-! # T-A2, part 1: the THR dimension `m_T` against the load `Ψ_T` (P3:3094-3107)

The stage (`ThrDim.mTG`) writes `m_T = mOfT K_L P + T` with `T = K_f·C_D·((k'+L)²·C_D·(⌈√(B_T·L)⌉+1+L²) + k' + L²)`
and `k' = r·natBitLength(n/r+1)`; the load is `Ψ_T = C_D((k+L)²·C_D(⌊√(B_T·L)⌋+1+L²) + k + L²)` (`loadThr`,
`d_T = C_D(√(B_T L) + L²)`, P3:3094-3100). At a star parameter (`4r ≤ n`, so `s = ⌊log₂(n/r+1)⌋ ≥ 1`):

* `kp_eq` (`k' = k + r`), `s_pos`, `r_le_k`, **`k_le_kp`**, **`kp_le_2k`** (`k ≤ k' ≤ 2k`);
* `sqrt_le_ncs`, `ncs_le_sqrt` (`⌊√X⌋ ≤ ⌈√X⌉ ≤ ⌊√X⌋ + 1`);
* `ge_shape`, **`m_geG`** (`mOfT + K_f·Ψ_T ≤ m_T`); `le_shape`, **`m_leG`** (`m_T ≤ mOfT + 8·K_f·Ψ_T`).

Paper quantity of the main types: the THR writer's dimension `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Transfer

/-! ## `k' ∈ [k, 2k]` -/

/-! ## The square roots -/

/-! ## The two dimension bounds -/

section Gate
variable (l : Literals) (F : GateFree l) (KL Kf : ℕ)

/-- **T-A2 `m_ge`**: the dimension covers the unit budget, `mOfT K_L P + K_f·Ψ_T(P) ≤ m_T(P)`. -/
theorem m_geG (P : Shared.StarParams) :
    PrimThrW.Shell2.mOfT KL P + Kf * ThrDim.psiT l F.CD P ≤ ThrDim.mTG l F KL Kf P := by
  show _ ≤ PrimThrW.Shell2.mOfT KL P +
    NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf
  apply Nat.add_le_add_left
  exact ge_shape F.CD Kf P.k (P.r * natBitLength (P.n / P.r + 1)) (Nat.clog 2 (P.n + 2))
    (ThrDim.bT l P * Nat.clog 2 (P.n + 2)) (k_le_kp P)

/-- **T-A2 `m_le`**: the dimension stays in the preprocessing class, `m_T(P) ≤ mOfT K_L P + 8·K_f·Ψ_T(P)`. -/
theorem m_leG (P : Shared.StarParams) :
    ThrDim.mTG l F KL Kf P ≤ PrimThrW.Shell2.mOfT KL P + 8 * Kf * ThrDim.psiT l F.CD P := by
  show PrimThrW.Shell2.mOfT KL P +
    NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf ≤ _
  apply Nat.add_le_add_left
  exact le_shape F.CD Kf P.k (P.r * natBitLength (P.n / P.r + 1)) (Nat.clog 2 (P.n + 2))
    (ThrDim.bT l P * Nat.clog 2 (P.n + 2)) (kp_le_2k P)

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB

end
