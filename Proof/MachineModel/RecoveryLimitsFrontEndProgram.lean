import Proof.MachineModel.CanonicalRecoveryValidatorProgram

/-!
# The limits front end of the recovery verifier

The internal validator ABI of `CanonicalRecoveryValidatorProgram` is
`pair(encoded schedule-derived limits, untrusted witness)`, and its comment
names the remaining obligation exactly: *the final public wrapper must build or
freeze the left component from register-one input arity; the nondeterministic
branch supplies only `raw`.*  This module is that wrapper.

The wrapper is a two-stage stream that is completely independent of *how* the
limits code is produced:

```
raw
  → recoveryLimitsDuplicateProgram            pair(raw, raw)
  → preserveRightProgram limitsCodeProgram    pair(limitsCode, raw)
```

`preserveRightProgram` forwards the public input length unchanged, so the
supplied `limitsCodeProgram` sees exactly `initialNPOracleState inputLength raw`
and may read the public arity from register one.  Consequently the whole
front-end obligation of `ExecutableRecoveryMachine.hlimitsFrontEnd` collapses
to the single premise

```
runNPOracleProgram limitsCodeProgram bits fuel
    (initialNPOracleState request.length (encodeBitInput request.witness)) =
  some (encodeRecoveryWitnessLimits (limitsOf request.inputArity))
```

which is `run_recoveryLimitsFrontEndProgram_request` below.  §4 discharges that
premise unconditionally for every *frozen* policy, i.e. whenever `limitsOf` is
constant: the frozen numeral is a `.set` immediate, so no arithmetic on the
public arity is performed at all.

## What a limits-code program can and cannot compute

`NPOracleProgram` is a finite list of instructions whose immediates are
naturals, and `run_bits_mono` makes a successful output independent of the
width budget.  A limits-code program therefore realizes a family
`inputLength ↦ encodeRecoveryWitnessLimits (limitsOf inputLength)` only when
that family is computable from the finitely many naturals frozen into the
stream.  §4 is the boundary case where the family is constant; a genuinely
length-indexed family must be presented the same way, as a program plus its run
theorem.  Nothing in this module assumes more.
-/

namespace NearCubicWires.RecoveryLimitsFrontEndProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 Duplicating the untrusted witness code

The nondeterministic branch supplies `raw` in register zero and nothing else.
Duplicating it is what lets the count-preserving adapter overwrite one copy
with the limits code while retaining the other. -/

/-! ## §2 The wrapper -/

/-! ## §3 The machine premise shape

`WeakVerifierRequest.length` is definitionally `WeakVerifierRequest.inputArity`,
so the public arity the machine indexes its policy by is exactly the register
the wrapper forwards. -/

/-! ## §4 The frozen policy

A frozen numeral is a `.set` immediate: the stream performs no arithmetic on
the public arity, so the run theorem holds at every input length and every
guessed code.  This closes `hlimitsFrontEnd` outright for a constant policy
family. -/

end NearCubicWires.RecoveryLimitsFrontEndProgram
