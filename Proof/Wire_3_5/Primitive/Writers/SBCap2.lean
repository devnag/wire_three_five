import Lean
import Proof.Wire_3_5.Primitive.Writers.SBCap1
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Primitive.Writers.SBCap2Base


noncomputable section
set_option maxRecDepth 4096


/-! # SB: the capacity target, part 2 — `sbNeed` polynomial in `|fpIn r| + 1`

* `ul_le` (the small-number word within `10^5·Z`), `sbNeed_Z` (every term of `sbNeed` against one majorant);
* `DD`, `KcF`, **`sbCap : StarRStmt l → SBCapStmt l`** (`sbNeed ≤ KcF l F·(N+1)^{DD l}` at every star request).

Donors: `CallIndexR.cap_leR`, `SymSizes.sparse_le_gate`/`TS4.spT_le`, `SymSizes.lambda_le`, `SymSizes.rowBt_le`,
`TS4.two_pow_le`, `FpInLen.n_le_fpIn`, the carriers' envelope.

Paper quantity of the main type: SB's capacity (`prim:runtime`, P3:3105-3115; "all powers of `n` are fixed before a
fixed `r`", P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.FinalPass.Out.Car NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

/-- **Every term of `sbNeed` against one majorant.** -/
theorem sbNeed_Z (l : Literals) (cr fe : ℕ) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc : ℕ) :
    sbNeed l cr fe P m wl c0 c1 nc ≤
      10 ^ 8 * ((P.n + 1) ^ 26 + Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2
        (gateCδ1 l) P.n) P.n + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) +
      SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq P.n)
        (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n - 1) +
      (2 ^ 40 * (CallIndexR.capK cr * (P.n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
        CapNum.cMain (gateCap l) m) +
      Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n + Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n +
      2 * wl + 2 ^ (natBitLength P.n + 1) + 2 ^ DtC * (wl + 1) ^ DtC + ((fe + 4) * (P.n + 3) + 2 * cr + 20) := by
  have hmb := mbOf_le m
  have t1 := tB1_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have t2 := tB2a_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have t3 := tB2b_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have t4 := tB2c_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have t5 := tC1_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have t6 := tC2_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have t7 := tC3_le P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 hmb
  have hu := ul_le P (Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2
    (gateCδ1 l) P.n) P.n) fe c0 c1 nc
  obtain ⟨-, -, -, -, -, -, -, a8, a9, a10, -, a12⟩ := atoms P fe 0
  have hl : 4 * ellOf P.n + 6 ≤ 8 * (P.n + 1) ^ 26 + 30 := by unfold ellOf; omega
  have he : fe * Nat.clog 2 (P.n + 2) / 4 + 2 ≤ fe * (2 * P.n + 4) + 2 := by
    have := Nat.div_le_self (fe * Nat.clog 2 (P.n + 2)) 4; omega
  unfold sbNeed
  generalize tB1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T1 at t1 ⊢
  generalize tB2a P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T2 at t2 ⊢
  generalize tB2b P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T3 at t3 ⊢
  generalize tB2c P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T4 at t4 ⊢
  generalize tC1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T5 at t5 ⊢
  generalize tC2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T6 at t6 ⊢
  generalize tC3 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 = T7 at t7 ⊢
  generalize (Data.unaryList (sbList P (Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l)
    (gateZeta_lt l) 2 (gateCδ1 l) P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length = U at hu ⊢
  generalize Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n)
    P.n = CAP at t1 t2 t3 t4 t5 t6 t7 hu ⊢
  generalize 2 ^ (natBitLength P.n + 1) = W at ⊢
  generalize 4 * ellOf P.n + 6 = EL at hl ⊢
  generalize fe * Nat.clog 2 (P.n + 2) / 4 + 2 = E2 at he ⊢
  clear * - t1 t2 t3 t4 t5 t6 t7 hu hl he a9
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
