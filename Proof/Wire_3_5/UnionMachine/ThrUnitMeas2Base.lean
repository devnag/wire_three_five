import Proof.Wire_3_5.UnionMachine.ThrUnitMeasBase
import Proof.Wire_3_5.FinalPass.ThrPtRS11
import Proof.Wire_3_5.Filters.FilterGap
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPolyBase

/-! # The THR unit's measure absorbed by `Ψ_T`, part 2: the FILTER setup's arguments and the data counts

At a THR call (`L = ⌈log₂(n+2)⌉`): the FILTER setup's arguments at every carrier row and star row (the THR filter's
length `2(n+1)^{26}`, cap `B_T ≤ 2^{(48+Z)L}`, error `f_e·L`, the slice and its offset within the pool, `4·row`, the
pool, the seeds `2^{seedBits}`, filt:gap P3:2019-2030) are `2^{K_F·L²}` uniformly in the gate (**`fArgs_le`**); the
data tape's counts (the sixteen THR numbers, `ThrNumsPoly`, and the carriers' and the tuple's sizes) are
`≤ (16K_t + 32)·2^{(D_t+26)L}` (**`u_le`**; `K_t` after the gate, `D_t` before).

Paper quantity: the THR unit's FILTER rows and data word, within `2^{O(Ψ_T)}` (P3:3094-3108). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (pow_N_le one_le_L n2_le_L pow_mono_mul)

theorem sliceOff_succ {α : Type} (ls : List (List α)) (j : ℕ) :
    Records.sliceOff ls (j + 1) = Records.sliceOff ls j + (ls.getD j []).length := by
  unfold Records.sliceOff
  rw [List.take_add_one, List.map_append, List.sum_append, List.getD_eq_getElem?_getD]
  cases ls[j]? <;> simp

theorem sliceOff_mono {α : Type} (ls : List (List α)) {j k : ℕ} (h : j ≤ k) :
    Records.sliceOff ls j ≤ Records.sliceOff ls k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [sliceOff_succ]; omega

section Call

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
