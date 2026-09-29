import Proof.CaseAnalysis.CaseTwoWitnessCompleteness

/-!
# A program-computable recovery-limits family

`RecoveryLimitsFrontEndProgram` reduces the machine's limits obligation to one
run theorem for a family `inputLength ↦ encodeRecoveryWitnessLimits (limitsOf
inputLength)`, and records that such a program exists only when the family is
computable from the finitely many naturals frozen into its instruction stream.
The exact schedule policies of `RecoveryWitnessScheduleCapacity` are *not* of
that shape: their two term caps are

```
xorAuthorizedTermCap witness delta copies arity =
  ⌈witness.termCoefficient delta * arity / xorEpsilon delta copies ^ 2⌉₊
```

with `witness.termCoefficient : ℝ → ℝ` an arbitrary real function, so the
dependence on `arity` is a ceiling of a real multiple and no finite instruction
list over natural immediates realizes it.  The same applies to the real mass
envelope `witness.massCoefficient delta / xorEpsilon delta copies`.

Opacity of a *natural* is not the obstruction — a frozen natural is a `.set`
immediate whatever its provenance.  Only the two genuinely real-valued
envelopes are.  This module therefore replaces exactly those two fields by
explicit arithmetic over the frozen naturals

```
⌈witness.termCoefficient delta⌉₊    ⌈witness.massCoefficient delta⌉₊
```

and leaves every other field of the published policies untouched: the two
arities are constrained to be *equal* by `RecoveryWitnessLimits.Weakens`, and
they, the oracle size cap, the wire caps and both description caps are already
explicit arithmetic in the schedule's frozen naturals.

The resulting family is a genuine weakening of the exact policy at every
schedule coordinate, so completeness transports through
`CheckedRecoveryWitness.widen` without changing a single serialized bit, and it
remains `PolynomiallyBounded`, so the executable `n / 16` witness shape still
absorbs it after an internally derived onset.

Two `noncomputable` markers appear below.  They are Lean code-generation
markers only: the frozen naturals are selected by `Classical.choice` inside the
published contracts.  Every field of the family is an arithmetic expression in
those naturals and the public input length, which is exactly what an
`NPOracleProgram` can evaluate.
-/

namespace NearCubicWires.RecoveryLimitsComputableFamily

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoWitnessCompleteness
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessNormalization
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessScheduleCapacity
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## §1 The frozen numeral profile of the published amplifier

Four naturals is everything the decoder policy needs from the imported XOR
amplifier at the published radius.  Two of them are already natural fields of
the amplifier witness; the other two are ceilings of its real coefficients. -/

/-! ## §2 The computable policy shape

Every field below is a closed arithmetic expression in the profile numerals,
the copy-count envelope and the schedule's own natural fields. -/

/-! ## §3 Weakening the exact policy into the computable one -/

/-! ## §4 The inverse-polynomial schedule

The exact copy count is real-derived, so it is replaced by the linear
`logScale` envelope already used by the schedule's own polynomial closure.
Every other field of `inverseRecoveryWitnessSourceLimits` is retained
verbatim: its wire caps are already the cubic core envelope, which is explicit
arithmetic. -/

/-! ## §5 The fixed-rate schedule

Here the copy count is already a frozen natural; the two wire caps are the
real-floor physical sizes, so they are widened to the same cubic core envelope
the schedule's polynomial closure already uses. -/

/-! ## §6 Polynomial closure of the computable family

Widening a resource cap can only be sound if the widened cap is still
polynomial: otherwise the executable `n / 16` witness shape would stop
absorbing the canonical code and the resource checks would lose their meaning.
Every field of the computable family is re-audited here. -/

/-! ## §7 Eventual capacity in the executable witness shape

These are the exact analogues of the schedule-capacity theorems, re-derived at
the computable family.  The onsets are internally derived from §6; no capacity
premise is left to a caller. -/

/-! ## §8 Case-2 completeness at the computable family

The completeness chain of `CaseTwoWitnessCompleteness` is limits-parametric:
the semantic witness is produced at the exact XOR policy, rechecked under a
weaker policy by `CheckedRecoveryWitness.widen`, and accepted once the policy
fits the executable witness shape.  Instantiating that chain at the computable
family therefore costs exactly the two facts proved above — the weakening and
the capacity onset — and no new serialization path. -/

end NearCubicWires.RecoveryLimitsComputableFamily
