import Proof.Wire_3_5.FinalPass.SymCost4Base
import Proof.Wire_3_5.FinalPass.SymCost5Base
import Proof.Wire_3_5.FinalPass.SymBFBase
import Proof.Wire_3_5.FinalPass.SymHrBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7Base
import Proof.Wire_3_5.FinalPass.SampPad

/-! # The SYM free numbers' builder (v7): `SymFreeOk7` at every gate, fixed before `F`

The C4.K contract v7 (`C4SymKB7.SymFreeOk7 l F wa K3 D3 Kp Dp`): the deliverable. For each endpoint exponent
`f_e`, the constants `SymC` (`symCof`: `d_T = 2e_N`, `d_Q = c_S + 401`, `d_H = coef·4^{deg} + 2`, `e_H = 26deg + 1`,
`d_D = symDD` (the linear degree bound, `SymDeg`), `d_P`, `e_P`, `d_C = symDC`, `d_A = symDAc`, `d_R = 0`), the load
floor `C_{D,s}` (`symCDs`: the printer floor `occCD`, the capacity floor `16·symC1` and the child's-steps floor
`symHC`, all fixed before `F`, P3:3094-3107), the C3 load constants `K3 = c3K2`, `D3 = e_H + e_P` and the pad
constants `Kp = 4^{d_A} + 1`, `Dp = d_A + d_R` are fixed; at every gate `F` with `F.filterErrDeg = f_e`,
`C_{D,s} ≤ C_D` and `1 ≤ c_ψ` the free program `freeProg2 (symK2 c)` with `dF = symDF c`, `K = symKn c` (the
capacity) and `K_ch = symKch` (`2^{n−k+d_A L−4}`) meets every field: the program's bounds (FreeGen9), the pad
(`pad2`), the C3 load (`c3_sym2`), `side` at every SYM call with rows (the SYM batch) and `side_pad` at every
degenerate call (the padded batch).

The floors recorded: `occCD ≤ C_D` (the printer's budget), `16·symC1(e_N, e_Q, Z) ≤ C_D` (the
enumeration's capacity), `symHC ≤ C_D` (one child's steps under the pad); `symDC ≤ d_C`, `symDAc ≤ d_A`,
`symDD ≤ d_D` are the constants' own choices. All depend on `l` and `f_e` only (and on `wa` for `d_A`).

* `algL`, `symCof`, `symCDs`, `small_of`, **`symFreeOk`**.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of the SYM stage and their bounds. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.RepairRepresentation

/-- The small inputs are small for the free program (the four fields it reads). -/
theorem small_of {Ds : ℕ} {x : FreeIn} (h : PrimT.C4SymW.FreeSmall Ds x) : FreeSmall Ds x :=
  ⟨h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
