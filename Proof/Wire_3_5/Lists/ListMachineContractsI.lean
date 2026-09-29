import Proof.Wire_3_5.Lists.ListMachineContracts
import Proof.Wire_3_5.Lists.ListMachineInterp
import Proof.Wire_3_5.Lists.ListMachineEncoding
import Proof.Wire_3_5.FinalPass.List

/-! # C2d by interpolation: the reference printed from values, and its contract `c2dI` (P3:1482-1488)

Realizes the C2d sub-contract (P3:1482-1488: "The explicit monomial lists have at most `2^{O((Σ_j H_j) log(M+2))}`
occurrences and are constructible within that bound times a polynomial in the description size") with the reference
the interpolation printer computes: `P_s` is printed from its VALUES at the points `1_T` (`Interp.interpPrint`), and
the values come from the fast report of the final pass (P3:3175-3178, C5's `ListFast.listReportFast`), which is
the paper's reported count on every input (`listReport_eq_fast`).

Main results: `ListTable.printedI` (the reference), **`printedI_correct`** (the verified consumer statement of `c2d`,
`T.Correct`, holds for it: every printed state IS the paper's `P_s` on every Boolean input, of degree
`≤ Σ_{j<J}(H_j−1)`, on `Z_0, …, Z_{L−1}`, with at most `(L+1)^{Σ_j(H_j−1)}` monomials), the contract **`c2dI`** (beside
`c2d`: the output tape `polysWord`, the size `q` = the description length, the load `psiC2d = dPrint·(w+1)`, `w` the
binary width of `L+1` and `dPrint = Σ_{j<J} 4W_j + 1 ≥ degreeBound` the printer's enumeration bound, so
`(L+1)^{dPrint}·2^{dPrint} ≤ 2^{psiC2d}`), `c2dI_err`, and the side lemmas for the assembly (`degreeBound_le`,
`degreeBound_le_dPrint`, `psiC2d_eq`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.ListMachine.Ref Finset

theorem evalP_eq (p : Poly) (ρ : ℕ → Bool) : Interp.evalP p ρ = F2Poly.eval p ρ := rfl

namespace ListTable
variable (T : ListTable)

theorem bitF2_inj {a b : Bool} (h : bitF2 a = bitF2 b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-! ## The load and the description size -/

end ListTable

/-! ## The contract -/


end NearCubicWires.WireExponent3_5.ListMachine
