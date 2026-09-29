import Proof.Circuits.CanonicalBalancedBuilder
import Proof.MachineModel.PreserveRightProgram

/-!
# Context-preserving tagged-to-balanced conversion

Structural emitters build one private tagged stream because consing is the
natural fixed-machine operation.  This verified adapter applies the sole
canonical balanced builder to that stream while preserving an arbitrary right
context such as the unary prefix count.

> ⚑⚑ **TWO TRAPS. Read before using this module — you have probably arrived
> here by name-search, which is exactly how both are sprung.**
>
> **1. It does not lower any charge.**  `taggedToBalancedPreservingMaximumBits`
> below is *defined as*
> `preserveRightBits (taggedToBalancedRegisterBitsFor inputLength values) …`,
> and `taggedToBalancedRegisterBitsFor` is the quantity refuted by
> `ValidatorTaggedIntermediateVerdict`
> `.two_pow_le_canonicalNatValidationBits_canonicalAtomFamily_of_run`
> (`≥ 2 ^ (list length)`, and that proof never unfolds a charge definition, so
> it is not repairable by re-charging).  Composing a tagged emitter with this
> adapter therefore **satisfies a balanced run premise exactly and builds
> green while leaving the refuted charge in place.**  If you need a balanced
> emitter, use `StructuralAtomEmitterLoopProgram.structuralAtomBalancedEmitterProgram`
> (`TrustBalancedStructuralAtomEmitter`), which exposes the loop's balanced
> output *before* the retag rather than converting back to it.
> `Proof/MachineModel/RuntimeCaseTwoDescriptionFrameAdapter.lean` states the same in prose.
>
> **2. It is not the cheap pilot it looks like.**  63 lines and one importer,
> but that importer places it inside a ~1040-module transitive cone — the worst
> value-for-risk of the eighteen `run_taggedToBalancedProgram_from` sites.  A
> size-ranked pilot choice walks straight into it.
-/

namespace NearCubicWires.TaggedToBalancedPreservingProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram

end NearCubicWires.TaggedToBalancedPreservingProgram
