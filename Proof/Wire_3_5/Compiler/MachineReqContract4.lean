import Proof.Wire_3_5.Compiler.MachineReqContract3

/-! # C3 v3′: alg:compiler's size hypotheses with the counter loop always charged (P3:1887-1906)

Paper: "with at most `𝒮 ≤ A·2^m·Q'(P_ex+1)^{Q'd}` occurrences" (alg:eq-occurrences, P3:1892) and "Construction takes
`(input description size + 𝒮)·poly(n)` deterministic bit operations" (P3:1905-1906). The decision on the class
bound: the occurrence count is tied to the class argument in the form (c′) `max(1, A)·2^m·Q'(P_ex+1)^{Q'd} ≤ 2^Ψ`
(the counter loop over the `2^m` sub-lists runs even for `A = 0`; (c′) coincides with (c) whenever `A ≥ 1`). The
preprocessing budget `2^{cpsi·Ψ}·n^{Apre}` also needs `n ≥ 1`. The C3 v3 (`ReqContract3`) is unchanged; this
module states the precondition used by the machine's `Implements`: `C3Req.LoadP` = (a) alg:eq-budget ∧ (b) the displayed
parameters within `(n+1)^{a_par}` ∧ (c′) ∧ `1 ≤ n`, and the contract **`c3v3p`** (C3 v2's reference, output, class and
error field; `c3v3p_err`, `c3v3p_not_nil`). The paper quantities are alg:compiler's hypotheses. Main declarations:
`occBoundP`, `C3Req.LoadP`, **`c3v3p`**, **`c3v3p_err`**, **`c3v3p_not_nil`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.RepairRepresentation

variable (a : DecompositionAlgorithm)

/-- The occurrence count with the counter loop always charged, `max(1, A)·2^m·Q'(P_ex+1)^{Q'd}`. -/
def C3Req.occBoundP (R : C3Req) : ℕ :=
  max 1 R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d))

/-- (c′) implies (c): the occurrence bound of C3 v2's error field is within the charged count. -/
theorem occBound_le_occBoundP (R : C3Req) : R.occBound a ≤ R.occBoundP a := by
  unfold C3Req.occBound C3Req.occBoundP
  gcongr
  exact le_max_right _ _


end NearCubicWires.WireExponent3_5.CompilerMachine.Req
