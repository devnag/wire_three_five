import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.UnionMachine.RadAbsorbBase

/-! # The THR unit machine's contract, v4: the measure absorbed by the THR load `Ψ_T` alone

`ThrUnit.ThrUnitSpec3` (THRU3) bounds the per-call measure by `2^{K·psiOf n}`, `psiOf = max(Ψ_T, Ψ_S, Ψ_aux)`
(P3:3106-3107); the THR shell (THRTAIL) dimensions its counters in-machine, so the SYM and auxiliary loads would enter
its dimension stage. Every term of the THR unit's measure is a THR quantity: the RADIX list bound is absorbed through
`ThrSide.loadThr_le` (`RadAbsorb.lb_absorb`'s own chain), the decode's `2^{K·L²}` through `L² ≤ C_D·L² ≤ Ψ_T`, the
THR cap `B_T` through `√(B_T·L) ≤ Ψ_T`. So the bound is stated against **the THR load**
`Ψ_T = loadThr C_D k L B_T` (P3:3094-3100, `k = kOf n`, `L = ⌈log₂(n+2)⌉`, `B_T = capOf .thr n`):

* `loadThr_le'`, **`lb_absorbT`**: the RADIX row's list bound times `L` below `cAb l · Ψ_T`;
* **`ThrUnitSpec4 l F`**: `ThrUnitSpec3` with `meas_le` against `Ψ_T`; `ThrUnitSpec4.toSpec3` (`Ψ_T ≤ psiOf`);
* `deg4`, `cf4`, **`ThrUnitU4 l`**, **`ThrLeafOfU4 l`**, **`ThrUnitOf5 l`** (the producer statement), `nU_tail`.

Paper quantity of the main type: the THR tape's units within the preprocessing class `2^{O(Ψ_T)}` (P3:3089-3108). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.Stars

/-! ## The RADIX list bound against the THR load -/

theorem loadThr_le' (CD k L BT : ℕ) :
    CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) ≤ loadThr CD k L BT := by
  unfold loadThr sqrtUp
  have e : CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) =
      CD * ((k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2))) := by ring
  rw [e]
  apply Nat.mul_le_mul_left
  have : (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2)) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + 1 + L ^ 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

/-! ## THRU4 -/

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
