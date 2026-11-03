import Proof.Wire_3_5.Primitive.Writers.SBCap2Base
import Proof.Wire_3_5.Primitive.Writers.SBFieldCostBase

/-! # SB: the capacity target, part 3 — **`sbCap : StarRStmt l → SBCapStmt l`**

`sbNeed ≤ KcF l F·(N+1)^{DD l}` at every star request (`N = |fpIn r|`): the phase sums, the cap
(`CallIndexR.cap_leR`), the sparse bound (`SymSizes.sparse_le_gate`, `TS4.spT_le`), `λ` (`SymSizes.lambda_le`), `t`
(`SymSizes.rowBt_le`), the counts (the envelope), the input length, the carrier pipeline's `2^{DtC}(N+1)^{DtC}`.

Paper quantity of the main type: SB's capacity (`prim:runtime`, P3:3105-3115; P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.FinalPass.Out.Car NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

theorem carCnt_le {n : ℕ} (cs : List (Stars.Carrier n)) (h : ∀ X ∈ cs, X.WithinEnvelope 26) (k : ℕ) :
    carCnt cs k ≤ (n + 1) ^ 26 := by
  unfold carCnt; split
  · exact (h _ (List.get_mem _ _)).1
  · exact Nat.zero_le _

theorem pow_up (N d D : ℕ) (h : d ≤ D) : (N + 1) ^ d ≤ (N + 1) ^ D := Nat.pow_le_pow_right (by omega) h

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm