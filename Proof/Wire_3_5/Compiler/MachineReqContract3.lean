import Proof.Wire_3_5.Compiler.MachineTopLoad

/-! # C3 v3: the C3 v2 contract with alg:compiler's own size hypotheses (P3:1874-1906)

Paper: alg:compiler, "If all displayed logarithmic and degree parameters are bounded by fixed polynomials in `n`, and
`log₂A + m + log₂Q' + Q'd·log₂(P_ex+1) ≤ n_out/100` (alg:eq-budget), the complete table of `V` is recoverable exactly
in `2^{n_out}poly(n)` time, plus construction of the explicit expanded expression. Construction takes
`(input description size + 𝒮)·poly(n)` deterministic bit operations" (P3:1896-1906), with
`𝒮 ≤ A·2^m·Q'(P_ex+1)^{Q'd}` (alg:eq-occurrences, P3:1892), and the printer's `U = 2^{n_out/2}` (P3:1734).

The: C3 v3 is C3 v2 (MC7) whose precondition adds exactly
* (a) alg:eq-budget, with `n_out = 2·dRow` (base's Request has `2^dRow` rows and `2^dRow` columns);
* (b) the displayed parameters `p, width, P_ex, h, Q', d` and the coefficient bits `b` are at most `(n+1)^{a_par}`,
  with `a_par` a constant of the contract;
* (c) the occurrence bound tied to the class argument: `A·2^m·Q'(P_ex+1)^{Q'd} ≤ 2^Ψ`.
The reference, the output, the class and the error field are C3 v2's, so `c3v3_err` is `c3v2_err`.

The machine's input word is the load record of T1 (`c3Input`): the unary parameters, C3a's two words, the expression
and the two framed header parts. The paper quantities are alg:compiler's hypotheses (`C3Req.Load`). Main declarations:
`nOut`, `C3Req.Load`, **`c3v3`**, **`c3v3_err`**, **`c3v3_not_nil`**, `c3Fields`, `c3Input`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation NearCubicWires.SupplierPrinter
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces

variable (a : DecompositionAlgorithm)

/-! ## The input word -/

/-- The fields of the machine's input record: `1^{Q'}`, `1^{P_ex}` (the pool shape's label count), `1^m`, `1^h`, `1^{p+1}`, `1^{width}`, C3a's pool
stream (word (1)) and children table (word (2)), the expression, and the two framed header parts. -/
def c3Fields (R : C3Req) : List (List Bool) :=
  [List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true,
    List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true,
    (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame,
    Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) [], R.V.flatMap Poly.termRec ++ [false],
    frame (natWord R.dRow ++ natWord (R.p + 1)),
    frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)]

/-- **The machine's input word**: the load record of the fields. -/
def c3Input (R : C3Req) : List Bool :=
  Top.loadRec (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true)
    (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true)
    (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame)
    (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false])
    (frame (natWord R.dRow ++ natWord (R.p + 1)))
    (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols))

/-- The input word is the fields, framed one after another. -/
theorem c3Input_eq (R : C3Req) : c3Input a R = (c3Fields a R).flatMap frame := by
  simp [c3Input, c3Fields, Top.loadRec]


end NearCubicWires.WireExponent3_5.CompilerMachine.Req
