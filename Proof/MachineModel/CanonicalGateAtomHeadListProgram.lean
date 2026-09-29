import Proof.MachineModel.CanonicalSignedAtomRequestProgram

namespace NearCubicWires.CanonicalGateAtomHeadListProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.CanonicalSignedGateEvaluationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §3 The three straight-line adapters

One index duplicator in front of the dispatcher, one head adapter, and one
index shift for the coordinate stage.  Nothing else is added: the coordinate
stage of §4 or §9 of `CanonicalSignedAtomRequestProgram` runs unchanged. -/

/-! ## §4 The dispatched per-index stage

The fixed tag dispatcher of `TaggedProgramChoice` branches on the duplicated
index: zero runs the head adapter, every other index runs the shift followed
by the coordinate stage supplied at link time. -/

/-! ## §5 The head list over an arbitrary coordinate stage

Mapping §4 across a generated range one longer than the gate's arity is the
whole head list.  The generator, the projection, and the balanced call are the
§10 builder of `CanonicalSignedAtomRequestProgram`, restated by §1 at the
gate's own arity. -/

/-! ## §6 The uniform head list

Instantiating §5 at the uniform coordinate stage of
`CanonicalSignedAtomRequestProgram` §4 compiles the head lists of
`gateEvaluationLeftAtoms`, `gateEvaluationRightAtoms` and
`residualConstantRightAtoms`'s uniform halves. -/

/-! ## §7 The frozen head list

The same instantiation at the frozen coordinate stage of §9 compiles the head
list of `residualConstantRightAtoms` and of the frozen block of
`residualConstantLeftAtoms`. -/

/-! ## §8 The head lists the machine names

Instantiating the code list at a gate's canonical weight syntax identifies the
executed list with `signedAtomRequests` of the gate's own atom list: the
threshold atom followed by the coordinate atoms, exactly the shape
`run_signedAtomTotalProgram` consumes. -/

/-! ## §9 Two coordinate blocks under one head

`residualConstantLeftAtoms` is the only atom list of
`CanonicalSignedGateEvaluationProgram` whose head is followed by *two*
coordinate blocks,

```text
    (gate.threshold, 0, true) ::
      (gateAtoms gate 1 (liveSelector liveMask) ++
        gateAtoms gate 1 (frozenSelector inputMask liveMask))
```

Both blocks are the frozen coordinate stage: taking the live mask of the frozen
pair to be zero recovers the uniform selector, so the two blocks differ only in
the mask pair carried beside the shared weights.  The coordinate stage handed
to §4 is therefore one more tag dispatch, on `index + 1 - n`, which is zero
exactly on the first block. -/

/-! ## §10 The two-block coordinate stage -/

/-! ## §11 The two-block head list at the frozen stage

Both blocks of `residualConstantLeftAtoms` run the frozen coordinate stage:
the first with the live mask paired against zero, which is the uniform live
selector, the second with the genuine mask pair. -/

/-! ## §12 The two-block head list the machine names -/

/-! ## §13 The four atom lists of one gate's residual variable

`CanonicalSignedGateEvaluationProgram` §8 builds `residualVariableInput` from
exactly four balanced request lists.  Each is one instance of §6, §7 or §11 at
the gate's own weight syntax. -/

/-! ## §14 One gate's residual variable request, assembled

`residualVariableInput` is a pair of pairs of balanced list codes, so the whole
assembly is two paired calls of §13's list producers.  The two lists of a half
are produced by different programs exactly once — on the constant half — and
that is absorbed by one fixed tag dispatcher, so no producer is duplicated. -/

end NearCubicWires.CanonicalGateAtomHeadListProgram
