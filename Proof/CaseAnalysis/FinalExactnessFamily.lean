import Proof.CaseAnalysis.FinalExactness

/-!
# Constraint 18 — `CoordinateExpands` at `CloseoutWitness.SumFamily.value`

Paper C.10 (paper.tex:4104–4105): *"All expressions have degree at most four in
the **guessed sums**."*  The guessed sums are `CloseoutWitness.SumFamily`: one
rational linear combination of supplier circuits per PCPP variable.  P3a
(`RepairCloseoutFinalC10Exactness`) states its exactness theorems over the
generalized seam `CoordinateExpands pcpp evaluate proofValue coordinate` —
each recovered PCPP coordinate is ONE linear polynomial in supplier circuits.
This module discharges that seam at the honest family presentation, so P3a
composes with E1's `SumFamily` payload and not only with the occurrence slice.

Two obstacles, both closed here:

* **the arity cast.**  `SumFamily.value` evaluates each term at
  `fun j => u (Fin.cast (family.getSum i).arity_eq j)`, because a checked legal
  sum carries its own arity `value.q` together with
  `arity_eq : value.q = limits.expectedArity`, while `CoordinateExpands` wants a
  single `evaluate : Atom → BitInput n → Bool`.  `transportTerms` moves the term
  list along that equality and `transportTerms_value` shows the move is value
  preserving (`subst`, then `rfl`).
* **`variableCount` versus `pcpp.systematicBits + pcpp.auxiliaryBits`.**  Carried
  as an explicit `hvariables` and discharged by `Fin.cast`;
  `coordinateExpands_sumFamily_matched` is the cast-free instance, which is the
  spelling E1c will use.

No new constant, atom or codec is introduced: the coordinate polynomial is
literally `linearPolynomial` of the family's own transported term list.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The arity transport of a legal term list -/

/-! ## §2 The coordinate polynomial of the guessed sums -/

/-! ## §3 The seam -/

/-! ## §4 P3a, instantiated at the guessed sums -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
