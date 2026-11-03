import Proof.Wire_3_5.FinalPass.HashCost2Base
import Proof.Wire_3_5.FinalPass.HashOccBase
import Proof.Wire_3_5.FinalPass.HashPre1Base
import Proof.Wire_3_5.Primitive.Writers.ThrSide6Base
import Proof.Wire_3_5.FinalPass.HashPadBase
import Proof.Wire_3_5.FinalPass.EnumCap7

/-! # The HASH child's cost, part 3: `hcost` at a THR call's HASH stage

P3:2253-2290, 3011-3016, 3098-3107: one HASH child (`hCoreCost`: the Hb prep, the Hb printer's `n` cells at the
cell bound `K_c = Cap = 2^{⌊n/16⌋ + d_C L²}`, the expression's terminator, C6's assembler and the printer child) runs
within `K_ch = symKch = 2^{n − k + d_A L − 4}` steps at every prefix of at most `s_h = 2tℓ₀` bits, from T3's
`HbPrepBound`, the Hb size `hbS ≤ 2^{2k + c_S X³}` below the capacity (`capS_hash`, which also gives the printer's
cell bound `2^{32}(hbS+1)^8 ≤ Cap`), the `asmCost_le`/`childCost_le` at `q = 2^{e_C}·2^{e_X}`, `c3Cost_le_B`,
the charged occurrences `≤ 2^{C₁ S_aux}` and the `kch_pow` (at `d_A − 1`), under the floors `occCDH`, `costCDH ≤ C_D`
and `dAH ≤ d_A` (all fixed before `F`).

* `aux_le`, `fixH_le`, `occP_hash`, **`capS_hash`**, **`hcost_hash`**.

Paper quantity of the main type: one HASH child's step count against the pad. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.WireExponent3_5.CompilerMachine.Top NearCubicWires.RepairRepresentation

/-- `X³ ≤ 8·S_aux`, `k ≤ S_aux`, `L² ≤ S_aux`. -/
theorem S_facts (K L : ℕ) (hL1 : 1 ≤ L) :
    (L + 1) * (L + 1) * (L + 1) ≤ 8 * (K + L ^ 2 + (K + L ^ 3) * L ^ 2 * (K + L)) ∧
      K ≤ K + L ^ 2 + (K + L ^ 3) * L ^ 2 * (K + L) ∧ L * L ≤ K + L ^ 2 + (K + L ^ 3) * L ^ 2 * (K + L) := by
  have hLL1 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h1 : L ^ 3 ≤ (K + L ^ 3) * L ^ 2 * (K + L) := by
    calc L ^ 3 = L ^ 3 * 1 * 1 := by ring
      _ ≤ (K + L ^ 3) * L ^ 2 * (K + L) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hLL1) (by omega)
  have h2 : (L + 1) * (L + 1) * (L + 1) ≤ 8 * L ^ 3 := by
    have h3 : L + 1 ≤ 2 * L := by omega
    calc (L + 1) * (L + 1) * (L + 1) ≤ (2 * L) * (2 * L) * (2 * L) := Nat.mul_le_mul (Nat.mul_le_mul h3 h3) h3
      _ = 8 * L ^ 3 := by ring
  have e : L * L = L ^ 2 := by ring
  refine ⟨by omega, by omega, by rw [e]; omega⟩

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
