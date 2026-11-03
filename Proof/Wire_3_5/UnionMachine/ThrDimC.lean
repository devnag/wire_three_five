import Lean
import Proof.Wire_3_5.UnionMachine.ThrDimN
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.NumsXT2Gate
import Proof.Wire_3_5.Primitive.Writers.ThrDimIface
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.UnionMachine.ThrDimCBase


noncomputable section
set_option maxRecDepth 4096


/-! # T-A2, part 3: the stage's steps `c2G` within `K_c·(W+n+1)^{D_c}`, `D_c` fixed by `l`

The stage's steps `2·numsStageCostT2 W P … + 2` (the fill `W`, the reader, phases A–C, the tail) at the capacity
`2W + 2`: every piece is a polynomial in the atoms (`W`, `n`, `c_r`, `t`, `Λ̄`, `B_T·L`, `k'`, `C_D`, `K_f`, `K_L`, `s_p`)
of degree `≤ 6`, and every atom is below `Y_c = 2W + 4 + Y` (`Y = YB`, part 2) at EVERY star parameter:

* `sq_le'`, `stepCost_le'`, `qA_le`, `qB1_le`, `qB_le`, `qC_le`, `tail_le`, `head_le`, **`c2_Y`** (`c2G ≤ K_{c0}·Y_c⁶`);
* `yc_le` (`Y_c ≤ c_c·(W+n+1)^{Z_Y}`), **`DcG`** (`l` only), **`KcG`**, **`c2_leG`** (T-A2's `c2_le`).

Paper quantity of the main type: the THR dimension stage's running time, polynomial in the fill and `n`
(prim:runtime P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Transfer

section Pieces

end Pieces

/-! ## The stage's steps -/

section Cost
variable (l : Literals) (F : GateFree l) (KL Kf : ℕ)

/-- The steps' master bound at the fill `W`. -/
noncomputable def Yc (W n : ℕ) : ℕ := 2 * W + 4 + YB l F KL Kf n

theorem c2_Y (W : ℕ) (P : Shared.StarParams) : ThrDim.c2G l F KL Kf W P ≤ Kc0 * Yc l F KL Kf W P.n ^ 6 := by
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = Yc l F KL Kf W P.n := ⟨_, rfl⟩
  rw [← hYd]
  have hYB : YB l F KL Kf P.n ≤ Y := by rw [hYd]; unfold Yc; omega
  have hY1 : 1 ≤ Y := by rw [hYd]; unfold Yc; omega
  obtain ⟨p12, p23, p36⟩ := pw_chain Y hY1
  have hcap : 2 * W + 2 + 2 ≤ Y := by rw [hYd]; unfold Yc; omega
  have hn : P.n + 2 ≤ Y := (yb_n l F KL Kf P.n).trans hYB
  have hn3 : P.n + 3 ≤ Y := by
    have := yb_n l F KL Kf P.n; rw [hYd]; unfold Yc; omega
  have hcr : F.cr ≤ Y := (yb_cr l F KL Kf P.n).trans hYB
  have hKL : KL ≤ Y := (yb_KL l F KL Kf P.n).trans hYB
  have hCD : F.CD ≤ Y := (yb_CD l F KL Kf P.n).trans hYB
  have hKf : Kf ≤ Y := (yb_Kf l F KL Kf P.n).trans hYB
  have ht : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n + 5 ≤ Y := (yb_t l F KL Kf P.n).trans hYB
  have hΛ : Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n ≤ Y := (yb_lam l F KL Kf P.n).trans hYB
  have hB : ThrDim.bT l P ≤ Y := (yb_B l F KL Kf P).trans hYB
  have hX : ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2 ≤ Y := (yb_X l F KL Kf P).trans hYB
  have hD := (yb_D l F KL Kf P).trans hYB
  have hkp := (yb_kp l F KL Kf P).trans hYB
  have hsp := (yb_sp l F KL Kf P.n).trans hYB
  have hA := qA_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (2 * W + 2) Y P F.cr hcap hn hcr ht hΛ
  have hB1 := qB1_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (2 * W + 2) Y P hcap hn
  have hBB := qB_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) (2 * W + 2) Y P F.CD Kf hcap hn hX hkp
    hCD hKf hsp
  have hC := qC_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) Y P F.CD Kf hY1 hn hB hX hD hkp hCD hKf
  have hT := tT_shape (P.r * natBitLength (P.n / P.r + 1)) (Nat.clog 2 (P.n + 2))
    (CanonicalFourfoldRowProgram.natCeilSqrt (ThrDim.bT l P * Nat.clog 2 (P.n + 2))) F.CD Kf Y hY1 hkp hD hCD hKf
  have hTl := tail_le (2 * W + 2) Y P KL F.cr
    (NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf) hcap hn hcr hKL hT
  have hH := head_le Y P.n hn3
  have hW : W ≤ Y := by rw [hYd]; unfold Yc; omega
  show 2 * (11 * W + 20 + 1 + 1 + 1 + ((natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) + 1 +
    (NumsXT2.qACost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.cr + 1 +
      (NumsXT2.qB1Cost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) + 1 +
        (NumsXT2.qBCost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf + 1 +
          NumsXT2.qCCost P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf)) + 1 +
      NumsXS.tailCost (2 * W + 2) P KL F.cr
        (NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf)))) + 2 ≤ _
  unfold Kc0
  generalize NumsXS.tailCost (2 * W + 2) P KL F.cr
    (NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf) = a5 at hTl ⊢
  generalize NumsXT2.qCCost P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf = a4 at hC ⊢
  generalize NumsXT2.qBCost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf = a3
    at hBB ⊢
  generalize NumsXT2.qB1Cost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) = a2 at hB1 ⊢
  generalize NumsXT2.qACost (2 * W + 2) P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.cr = a1
    at hA ⊢
  generalize (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) = a0 at hH ⊢
  generalize Y ^ 2 = Y2 at p12 p23 hB1 hH ⊢
  generalize Y ^ 3 = Y3 at p23 p36 hA hBB ⊢
  generalize Y ^ 6 = Y6 at p36 hC hTl ⊢
  ring_nf
  omega

/-- The steps' master bound against `W + n + 1`. -/
noncomputable def cc (l : Literals) (F : GateFree l) (KL Kf : ℕ) : ℕ := 6 + cY l F KL Kf * 2 ^ ZY l

theorem yc_le (W n : ℕ) : Yc l F KL Kf W n ≤ cc l F KL Kf * (W + n + 1) ^ ZY l := by
  have hZ : 1 ≤ ZY l := by unfold ZY; omega
  have hV : W + n + 1 ≤ (W + n + 1) ^ ZY l := by
    calc W + n + 1 = (W + n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hZ
  have hN : (n + 2) ^ ZY l ≤ 2 ^ ZY l * (W + n + 1) ^ ZY l := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have hY : YB l F KL Kf n ≤ cY l F KL Kf * 2 ^ ZY l * (W + n + 1) ^ ZY l := by
    unfold YB; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hN
  unfold Yc cc
  have e : (6 + cY l F KL Kf * 2 ^ ZY l) * (W + n + 1) ^ ZY l =
      6 * (W + n + 1) ^ ZY l + cY l F KL Kf * 2 ^ ZY l * (W + n + 1) ^ ZY l := by ring
  rw [e]
  omega

/-- **The steps' exponent** (the literals only). -/
noncomputable def DcG (l : Literals) : ℕ := 6 * ZY l

/-- **The steps' coefficient** (after `F`, `K_L`, `K_f`). -/
noncomputable def KcG : ℕ := Kc0 * cc l F KL Kf ^ 6

/-- **T-A2 `c2_le`**: the stage's steps within `K_c·(W+n+1)^{D_c}`, `D_c = DcG l`. -/
theorem c2_leG (W : ℕ) (P : Shared.StarParams) :
    ThrDim.c2G l F KL Kf W P ≤ KcG l F KL Kf * (W + P.n + 1) ^ DcG l := by
  refine (c2_Y l F KL Kf W P).trans ?_
  have h := Nat.pow_le_pow_left (yc_le l F KL Kf W P.n) 6
  calc Kc0 * Yc l F KL Kf W P.n ^ 6 ≤ Kc0 * (cc l F KL Kf * (W + P.n + 1) ^ ZY l) ^ 6 := Nat.mul_le_mul_left _ h
    _ = KcG l F KL Kf * (W + P.n + 1) ^ DcG l := by unfold KcG DcG; rw [mul_pow, ← pow_mul]; ring

end Cost

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB

end
