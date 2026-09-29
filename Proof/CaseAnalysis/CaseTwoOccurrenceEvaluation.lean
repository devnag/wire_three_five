import Proof.MachineModel.CanonicalBitSliceProgram
import Proof.CaseAnalysis.CaseTwoOccurrenceSpecification

/-!
# Natural-number specification of one Case-2 occurrence value

`CaseTwoOccurrenceSpecification.caseTwoSeed_apply_executable` reduces one
scheduled Case-2 seed bit to

```
executableOccurrenceValue (caseTwoFactoryPCPP pcppSource caseTwo)
  (caseTwoOccurrenceCoordinates pcppSource caseTwo point)
```

whose right-hand side is still phrased in the dependent PCPP vocabulary:
`Fin`-indexed shape fields, a `Finset (Fin n)` support, a `TwoLiteralClause`,
and a `Literal`.  A fixed `NPOracleProgram` cannot consume any of those.

This module removes that vocabulary without changing the value.  Everything
below is stated over natural numbers and `Bool`, and every factory access is
one `PolynomialNatProgram.execute` call on an explicitly named request:

* `occurrenceShapeCode` — the single `shapeRunner` call;
* `occurrenceClauseCode` — the single `clauseRunner` call;
* `occurrenceSupportCode` — one `supportRunner` call per systematic index;
* `occurrenceHonestCode` — the single `honestRunner` call.

`executableOccurrenceValue_eq_occurrenceValue` is the resulting exact
specification.  `parityOn_decodeSupport_eq_maskFold` is the one non-mechanical
step: it converts the semantic parity over a decoded `Finset` support into the
masked exclusive-or fold over `List.range n` that the balanced parity
substrate of `CanonicalTaggedParityProgram` actually computes.
-/

namespace NearCubicWires.CaseTwoOccurrenceEvaluation

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The parity bridge

`parityOn` folds exclusive-or over `Finset.toList` of a decoded support, while
every executable parity stage folds over the flat index range `0, …, n - 1`.
The two agree because both count the selected `true` positions modulo two. -/

/-! ## 2. Factory calls in natural-number coordinates

The dependent shape fields of `factory.forCircuit circuit` are kept as the
official spelling of every width, so that no statement below carries two
defeq-but-distinct arities.  Their natural-number readouts from the single
shape-runner call are recorded separately in §3. -/

/-! ## 3. Widths read out of the single shape call -/

/-! ## 4. The exact specification -/

/-! ## 5. Occurrence coordinates of one public input code

The evaluator receives the requested occurrence point as a single natural
code.  These three identities are the whole coordinate ABI: the PCPP input is
the low digit window, the clause address is the interior window computed by
`CanonicalBitSliceProgram`, and the occurrence position is one digit read. -/

end NearCubicWires.CaseTwoOccurrenceEvaluation
