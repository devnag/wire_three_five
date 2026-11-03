import Lean
import Proof.Wire_3_5.Primitive.Writers.SBFieldCostBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.SBLay
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Primitive.Writers.SBCostBase


noncomputable section
set_option maxRecDepth 4096


/-! # SB: P1's cost target, proved

* the phases' costs within `300·sq cap + 3·(the phase's capacity sum) + 100` (`b1Cost_le` … `c3Cost_le`);
* `aCost_le` (phase A within `10^7·cap^3`), `parseCost_le` (within `5000·cap^2`), `emitListCost_le`;
* **`sbP1Cost : SBCostStmt l`** (`p1Cost ≤ 10^9·cap^3` once `sbNeed ≤ cap`).

Paper quantity of the main type: SB's budget (`prim:runtime`, P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums

section Phases

end Phases

theorem rowBt_of_need (l : Literals) (cr fe : ℕ) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ)
    (h : sbNeed l cr fe P m wl c0 c1 nc ≤ cap) : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n ≤ cap := by
  unfold sbNeed at h
  generalize 2 ^ (natBitLength P.n + 1) = Y at h
  omega

/-- **P1's cost target, proved.** -/
theorem sbP1Cost (l : Literals) : SBCostStmt l := by
  refine ⟨10 ^ 9, 3, fun F P m wl c0 c1 nc X h => ?_⟩
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, hpw, hcS, hcP, hcN, hlam, hwl, hcn, hc0, hc1, hnc, hE6, hE7, hfl, hcar⟩ :=
    need_parts l F.cr F.filterErrDeg P m wl c0 c1 nc X h
  have hX : 20 ≤ X := by clear * - hcS; omega
  have hCN := capNeed_mode l F.cr m P.n X hcN
  have hA := aCost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg F.cr (by omega) hcS
    (rowBt_of_need l F.cr F.filterErrDeg P m wl c0 c1 nc X h) hCN.hL1 hlam hCN.hs
  have hP := parseCost_le X wl P.n hX hwl hcn
  have hQ := sq_le X (by omega)
  have hX2 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hX1 : X ≤ X ^ 3 := by have := Nat.pow_le_pow_right (show 1 ≤ X by omega) (show 1 ≤ 3 by norm_num); rwa [pow_one] at this
  have hE := emitListCost_le (sbList P (Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2
    (gateCδ1 l) P.n) P.n) (F.filterErrDeg * Nat.clog 2 (P.n + 2)) c0 c1 nc)
  have b1 := b1Cost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  have b2 := b2aCost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  have b3 := b2bCost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  have b4 := b2cCost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  have b5 := c1Cost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  have b6 := c2Cost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  have b7 := c3Cost_le X P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg (mbOf m) nc c0 c1
  unfold p1Cost
  generalize UnaryPow.sq X = Q at hQ b1 b2 b3 b4 b5 b6 b7 ⊢
  generalize X ^ 3 = X3 at hA hX2 hX1 ⊢
  generalize X ^ 2 = X2 at hP hQ hX2 ⊢
  clear * - hA hP hQ hX2 hX1 hE b1 b2 b3 b4 b5 b6 b7 t1 t2 t3 t4 t5 t6 t7 hc0 hc1 hnc hE6 hE7
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
