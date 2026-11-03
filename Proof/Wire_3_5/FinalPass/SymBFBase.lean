import Proof.Wire_3_5.FinalPass.SymCap2Base
import Proof.Wire_3_5.FinalPass.SampPre

/-! # The SYM batch's facts at a call (for `hpre_sym`, `symHcost_of`)

P3:2477-2496 (row:sym) and P3:3011-3016 at a SYM call: the SYM batch (`symExprs`, `R = |carriers| + 2a′` rows
per entry) meets `SampShape.BatchFacts` with the factor counts `f r = 1` (filter rows) or the walk `w` (population
rows) (`sym_rows_factors`), the degree bound `symDg` and the atoms `< |flips|·|pool|` (`sym_factors_ok`), `±1`
coefficients (`sym_coef_pm1`) and at most `T = (M+1)²2^w ≤ 2^{63(k+L)}` terms per row (`sym_row_terms_le`); the
child's factor count `8·Σ_r f r` is the free number `m` whenever the call has rows (`sym_hmf`), and `8` (= `m`, the
padded batch's single constant row) at a degenerate call (`pad_hmf`).

* `symF`, `sum_split`, **`symBatchFacts`**, **`symT_le`**, **`sym_hmf`**, **`pad_hmf`**.

Paper quantity of the main type: the SYM rows' shape at a call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

theorem sum_split (N M w : ℕ) : ((List.range (N + M)).map fun r => if r < N then 1 else w).sum = N + M * w := by
  rw [List.range_add, List.map_append, List.sum_append]
  have h1 : ((List.range N).map fun r => if r < N then 1 else w).sum = N := by
    rw [List.map_congr_left (g := fun _ => 1) (fun r hr => if_pos (List.mem_range.mp hr))]
    simp
  have h2 : (((List.range M).map (N + ·)).map fun r => if r < N then 1 else w).sum = M * w := by
    rw [List.map_map, List.map_congr_left (g := fun _ => w) (fun r _ => by simp)]
    simp
  rw [h1, h2]

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
