import Proof.CaseAnalysis.FinalSupplierAccuracyChain
import Proof.CaseAnalysis.FinalTotalDecode
import Proof.CaseAnalysis.FinalThresholdRows
import Proof.CaseAnalysis.RowsEstimatorParitySymmetric

/-!
# The UNION supplier: one row preprocessor over both target classes at once

## The consumer, and why a single-class engine cannot serve it

`StageBlock.hpoint` (`Proof/CaseAnalysis/FinalStageContracts.lean`) quantifies
over `circuits : List (Atoms sources k x bits)`, i.e. over lists of
`C10TotalDecode.Atom (pcppOf ...)` (`Proof/CaseAnalysis/FinalTotalDecode.lean`),
a THREE-constructor union: `systematic`, `symmetric`, `threshold`.  The only
accuracy engine, `C10SupplierAccuracyChain.hpoint_of_rows`
(`Proof/CaseAnalysis/FinalSupplierAccuracyChain.lean`), is indexed by
`rows : FourfoldRowPreprocessor Circuit evaluate` at a SINGLE
`Circuit : CircuitFamily`, and every row preprocessor in the corpus sits either
at `NormalizedSymmetricThresholdCircuit` or at
`NormalizedThresholdThresholdCircuit`.  A mixed call list is in the image of
neither.

## Paper sentences this module realizes

**paper.tex:611** — "Both target classes contain parity below the displayed
caps.  For a symmetric top, use identity bottoms and the parity lookup."

**paper.tex:3679-3681** — "Every systematic code coordinate is a parity of at
most `q/2` inputs.  Realize it directly as a native `q`-input atom in the
selected target class: identity bottoms and a symmetric lookup use `O(q)`
wires, while cumulative threshold bottoms and alternating top weights use
`O(q^2)` wires."

**paper.tex:2322** — "Systematic code coordinates are compiled as native parity
atoms, so no half-arity supplier call is required."

**paper.tex:4106-4109** — "For a systematic row, realize `Enc_s` by the
explicit native parity circuit ... Expanding `(Enc_s - T_ij)^2` then uses only
constants, carried atoms, and conjunctions of one parity atom with at most one
carried atom; no parity-support enumeration occurs."

So the THIRD constructor is not a third estimation branch: the paper says the
systematic parity atom IS a native circuit of a target class, and
`normalizedParityCircuit` (`Proof/CaseAnalysis/RowsEstimatorParitySymmetric.lean`)
with `normalizedParityCircuit_eval` (`:144`) is that circuit.  The decode union
therefore maps into the TWO-class coproduct, and only two estimation branches
are needed.

**paper.tex:1369-1372** — "A degree-four expression in such sums and constants
expands into at most `(J+1)^4` AND-four calls.  Its propagated additive error is
at most `eta (1+Lambda)^4`."  The two branch errors are summed, and the summed
budget is `SupplierEstimator.reciprocalUnionBudget`'s own reservation at family
size one.

## What is constructed here, and what is NOT

`unionRows` is a genuine COPRODUCT of row preprocessors:

* `rowCount` is the PRODUCT of the two branch row counts, so it depends on the
  request's accuracy demand through both branches;
* `failure` is the SUM of the two branch failures, hence nonzero whenever either
  branch's is;
* `row` is the conjunction of one left row and one right row;
* `pointwise` is mismatch subadditivity for `&&`.

In particular the degenerate "exact" preprocessor (`rowCount := 1`,
`row := conjunctionBit evaluate`, `failure := 0`) is NOT used and cannot arise:
`unionRows` inherits both branch row counts and both branch failures verbatim.
-/

namespace NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The coproduct family -/

/-! ## §2 Splitting a mixed request

A `FourfoldRequest` (`Proof/Foundations/SupplierPipeline.lean`) is an arity and a
LIST of circuits at that arity, so a request at the union family is a MIXED
list: it is not the image of a request at either branch.  It is however the
JOIN of one request per branch, and the AND-four conjunction factors along that
join. -/

/-! ## §3 The analytic core: mismatch subadditivity for `&&` -/

/-! ## §4 THE COPRODUCT -/

/-! ## §5 The requested accuracy: one reservation, two branches

`SupplierEstimator.reciprocalUnionDenominator` (`Proof/Supplier/SupplierEstimator.lean`)
reserves a factor of two on top of the caller's requested reciprocal accuracy;
at family size one that is exactly the reservation two summed branch errors
need. -/

/-! ## §6 The decode union maps into the two-class coproduct

Paper A.8 (`paper.tex:2322`) and C.10 (`paper.tex:4106-4109`): the systematic
code coordinate is not a supplier mode of its own, it is the explicit native
parity circuit.  `normalizedParityCircuit` is that circuit in the symmetric
target class. -/

/-! ## §7 THE DELIVERABLE: `StageData.supplier` and `StageBlock.hpoint` at the
decode union -/

/-! ## §8 The concrete union supplier at the EIGHT SOURCES

SYM: `SupplierEstimator.symmetricFourfoldRows` over `EightSources.expander`.
THR: `CloseoutFinalC10ThresholdRows.thresholdRows` over `EightSources.expander`,
`EightSources.prime` and `EightSources.decomposition` -- the corrected carrier,
with no `ExecutableExactDecompositionAlgorithm`. -/


end NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
