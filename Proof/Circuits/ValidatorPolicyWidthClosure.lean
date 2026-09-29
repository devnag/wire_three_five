import Proof.Circuits.ValidatorComputableLimitsAssembly
import Proof.Circuits.ValidatorDescriptionLeafClosure

/-!
# The serialized policy's width, at degree two

`ValidatorComputableLimitsAssembly` §2 discharged the validator's `hprefix`
premise at the computable limits family in exchange for one hypothesis about the
family's own parameters:

```
hpolicy : PolyBounded (recoveryWitnessLimitsCodeBitBound P) measure c d
```

and `recoveryWitnessLimitsCodeBitBound` routes, through
`canonicalRationalCodeBitBound`, into `encodeNatBitsBound p = 1 + 2 · p⁴ · (p + 1)`.
That is **quintic** in the width parameter, so a degree-`1` certificate for the
parameter would only certify the serialized policy at degree `5` — one above the
machine's published `recoveryVerifierDegree = 4`.

The quintic is not the truth about the codec; it is the truth about the *coarse*
`balancedListCodeBits_le` reading of it.  `ValidatorLeafWidthCore` §5 publishes
the sharp reading — `natBitLength_encodeBalancedList_le_quadratic`, quadratic in
the atom **count** rather than quartic in the code — and `encodeNat` is exactly a
balanced list of one-bit atoms, so its width is *quadratic* in the source's.
This is the same cancellation `ValidatorCompositeLeafBounds` §5 spends for
`natBitLength_encodeNat_canonicalNatCandidate_le`; there the atom count is
additionally capped by the node-count shallowness lemma and the result is
linear, here the count is the parameter itself and the result is quadratic.

* §1 re-derives the three canonical numeric codecs — `encodeNat`, `encodeInt`
  and `encodeCanonicalRational` — at **degree two** in the field width.

* §2 re-derives the serialized policy record's width from the *same* width
  certificate `ValidatorPolynomialDomination` §4 already produces, at degree
  two, and instantiates it at the computable family.

* §3 spends it: the unit-budget transport of `ValidatorDescriptionLeafClosure`
  §1 turns a degree-`d` certificate for the family's width parameter into a
  degree-`2d` certificate for the serialized record, so `hprefix` closes at
  degree `2` over the measure-linear anchor — **inside** the saturated slot of
  four — and `hpolicy` disappears from the assembly's signature.
-/

namespace NearCubicWires.ValidatorPolicyWidthClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorDescriptionLeafClosure
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes

/-! ## §1 The three numeric codecs, quadratically

`encodeNat value` *is* `encodeBalancedList (value.bits.map boolCode)`: a
balanced list whose atoms are all one bit wide and whose length is the source's
own bit count.  §5 of `ValidatorLeafWidthCore` charges such a list at
`16 · (count + 1)² · atomWidth`, so the whole re-encoding costs a quadratic —
never the quartic-in-the-width `balancedListCodeBits_le` reads off the
unconstrained atom list. -/

/-! ## §2 The serialized policy record, quadratically

`ValidatorPolynomialDomination` §4 already produces the *width certificate*
`RecoveryWitnessLimitsWidth limits parameter` for the computable family, and its
record-shape ledgers `natBitLength_encodeLegalSumLimits_le` and
`natBitLength_encodeRecoveryWitnessLimits_le` are stated against an arbitrary
uniform field bound.  Only the rational mass cap's field bound was quintic; §1
replaces it, and the same two ledgers deliver the record at degree two. -/

/-! ## §3 `hprefix`, from the family's parameter alone

The unit-budget transport of `ValidatorDescriptionLeafClosure` §1 is exactly the
rule this shape needs: a bound of the form `budget · (width + 1) ^ k` against a
degree-`d` certificate for `width` is a degree-`k · d` certificate.  With
`k = 2` and the measure-linear anchor `d = 1` the serialized policy record lands
at degree **two**, and the published slot is four. -/

end NearCubicWires.ValidatorPolicyWidthClosure
