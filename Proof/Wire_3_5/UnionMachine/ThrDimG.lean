import Proof.Wire_3_5.UnionMachine.ThrDimC

/-! # T-A2, part 4: the THR dimension stage at the gate, `ThrDimStage l F K_L K_f (DnG l) (DcG l)`

`ThrDim.thrDimStage_of` (T-A1) at T-A2's four bounds, all at exactly `mTG`, `needG`, `c2G`:
`m_geG` (`mOfT + K_f·Ψ_T ≤ m_T`), `m_leG` (`m_T ≤ mOfT + 8·K_f·Ψ_T`), `need_leG` (`needG ≤ K_n(n+1)^{D_n}`),
`c2_leG` (`c2G ≤ K_c(W+n+1)^{D_c}`); the exponents `D_n = DnG l`, `D_c = DcG l` read the literals only, the
coefficients `K_n = KnG l F K_L K_f`, `K_c = KcG l F K_L K_f` come after `F`.

* **`thrDimStageG`** (the deliverable), `thrDimStageG_mT`, **`thrDim_exists`** (`∀ l, ∃ D_n D_c, ∀ F K_L K_f`, a
  stage: the exponents before the gate).

Paper quantity of the main type: the THR writer's dimension `2^{m_T}`, `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

/-- **T-A2's deliverable**: the THR dimension stage at the gate, its exponents `DnG l`, `DcG l` fixed by `l`. -/
noncomputable def thrDimStageG (l : Literals) (F : GateFree l) (KL Kf : ℕ) :
    ThrDim.ThrDimStage l F KL Kf (DnG l) (DcG l) :=
  ThrDim.thrDimStage_of l F KL Kf (DnG l) (DcG l) (m_geG l F KL Kf) (m_leG l F KL Kf) (KnG l F KL Kf)
    (need_leG l F KL Kf) (KcG l F KL Kf) (c2_leG l F KL Kf)

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
