import Statement_Wire_3_5
import Bindings.CLW20_Theorem1_13
import Proof.Circuits.PolynomialOrdinaryClock

/-! # Hypotheses 8 and 9 assume less than the printed statements

`Statement_Wire_3_5.lean` states CLW20 Theorem 1.13 and CLW20 Lemma 3.9 at the range the proof uses (hypotheses 8 and
9 of the main theorems). This file proves that each follows from the printed statement as transcribed in
`Statement.lean`, so each is a special case of it.
* `theorem1_13_poly_of_literal`: `CLW20_Theorem1_13 → CLW20_Theorem1_13_Poly`. Each clock `T(n) = n^(k+2)` is
  time-constructible and satisfies `n ≤ T(n) ≤ 2^{poly(n)}` (`clock_timeConstructible`, `clock_inClockRange`, applied
  to the polynomial clock `ordinaryClock k`), so the printed statement applies to it.
* `lemma3_9_large_of_literal`: `CLW20_Lemma3_9_TM2 → CLW20_Lemma3_9_TM2_Large`. The restricted statement keeps the
  printed constant `c` and asks for the amplifier only at the functions `S` with `n^c ≤ S(n)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.StatementChecks
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.Bindings.CLW20Theorem113

/-- CLW20 Theorem 1.13 as printed implies hypothesis 8: its conclusion at every clock `T(n) = n^(k+2)`. -/
theorem theorem1_13_poly_of_literal (h : CLW20_Theorem1_13) : CLW20_Theorem1_13_Poly := fun k =>
  h _ (clock_timeConstructible (RepairOrdinary.PolynomialClock.ordinaryClock k))
    (clock_inClockRange (RepairOrdinary.PolynomialClock.ordinaryClock k))

/-- CLW20 Lemma 3.9 as printed implies hypothesis 9: the same constant `c`, at the functions `S(n) ≥ n^c`. -/
theorem lemma3_9_large_of_literal (h : NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2) :
    CLW20_Lemma3_9_TM2_Large := by
  obtain ⟨c, hc, hS⟩ := h
  exact ⟨c, hc, fun S hT _ => hS S hT⟩

end NearCubicWires.WireExponent3_5.StatementChecks
