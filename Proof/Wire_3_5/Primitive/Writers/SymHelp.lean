import Lean
import Proof.Wire_3_5.Primitive.Writers.SymLeafIface
import Proof.Wire_3_5.Primitive.Writers.SymNums
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SymHelpBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (SYM leaf), part 9: the SYM call's sizes against the dimension

At a SYM call of the gate's family (`P = starParams n`, `L = ⌈log₂(n+2)⌉`, `k = kOf n`, the SYM cap `B_S`):

* **`sfam_mS`**: `m_S = k + L + K_F·L² + T` (`NumsXS.mS` at `D₂' = 26`, `K₀ = 6`);
* **`toQ`**: `(n+2)^d·2^{aL}·2^k·2^T ≤ 2^{m_S}` whenever `d + a ≤ K_F` (every size of the call is below the dimension);
* `sb_le` (the SYM filter's seed length `≤ 6000((26 + Z + fe)L + ⌈log₂(capK+1)⌉ + 4)`), `fbv_le` (the flat list's
  seed length `≤ (4Z + 4D₂ + 160)L + 888 + 4⌈log₂ capK⌉ + 4⌈log₂ C₂⌉`).

Paper quantities of the main types: the SYM writer's dimension `2^{m_S}` against the call's seeds and slices
(P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Transfer

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM dimension**: `m_S = k + L + K_F·L² + T`. -/
theorem sfam_mS {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) (KF : ℕ) :
    NumsXS.mS KF ((callInputs l F kclk coef A a ha).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l)
        (gateCap l) 26 6 =
      ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) + KF * Nat.clog 2 (n + 2) ^ 2 +
        SymSizes.tSOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) 26 6 (Nat.clog 2 (n + 2)) := by
  unfold NumsXS.mS PrimThrW.Shell2.mOfT NumsX.mOf
  rw [HashFam.fam_two_kh l F kclk coef A a ha hs]
  rfl

/-- The SYM cap: `B_S ≤ capK c_r·(n+2)^Z`. -/
theorem sfam_capS (n : ℕ) :
    ((gate0 l F).budget kclk coef A a ha).capOf .sym n ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l :=
  CallIndexR.cap_leR l F.cr .sym n

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam

end
