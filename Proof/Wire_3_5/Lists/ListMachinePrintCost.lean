import Proof.Wire_3_5.Lists.ListMachinePrintLoop

/-! # C2p, the printer's cost (P3:1482-1488, 3106-3115)

Realizes the construction bound of the explicit lists for the interpolation printer: the paper's lists are
"constructible within that bound times a polynomial in the description size" (P3:1482-1488), in the additive
preprocessing class `2^{O(Ψ)}` (P3:3106-3115). The printer visits at most `(L+1)^d` supports (`goods_length_le`),
each with at most `2^d` evaluations and `O(L²)` bookkeeping, so

  `printCost E d ≤ (L+1)^d · 2^d · (E.cost + 100(L+1)²) + 3`   (**`printCost_le`**). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5

theorem goods_length_le (L d : ℕ) : (Interp.goods L d).length ≤ (L + 1) ^ d := by
  have h := Interp.length_supports_le L d (Interp.monos L d) (Interp.monos_nodup L d)
    (fun S hS => ⟨(Interp.mem_monos hS).2.1, (Interp.mem_monos hS).2.2⟩)
  rwa [Interp.monos_eq_goods, List.length_map] at h


end NearCubicWires.WireExponent3_5.ListMachine.Print
