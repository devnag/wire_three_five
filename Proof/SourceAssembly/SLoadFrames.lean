import Proof.SourceAssembly.SLoadCore

/-! The suffix's framing pass.

`Request.input` is the concatenation of five frames. This module builds that
exact word on one ambient scratch tape out of five retained framed sources by
five paid calls of the existing three-tape frame appender
(`CompetitorFrameAppend.machine`, run by `CloseoutRowsCircuitAppend.frame_run`).
The appender's source cursor and reset log are physically restored, so the five
calls chain with no re-entry cost; only the growing output cursor advances. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Frames
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.CloseoutRowsCircuitAppend
noncomputable section

/-- Source slot, shared growing output slot, shared reset log slot. -/
def ports {U : Nat} (source out log : Fin U) : Fin 3 → Fin U := ![source, out, log]

@[simp] theorem ports_zero {U : Nat} (source out log : Fin U) : ports source out log 0 = source := rfl
@[simp] theorem ports_one {U : Nat} (source out log : Fin U) : ports source out log 1 = out := rfl
@[simp] theorem ports_two {U : Nat} (source out log : Fin U) : ports source out log 2 = log := rfl

/-- One fixed frame-append stage, a four-state local program docked at three
ambient slots. Neither the tape count nor the state count depends on a request. -/
noncomputable def stage {U : Nat} (source out log : Fin U) : Machine U 4 :=
  RecoveryFocus.machine (ports source out log) CompetitorFrameAppend.machine

/-- The fixed framing program: five docked appenders, twenty states. -/
noncomputable def machine {U : Nat} (s0 s1 s2 s3 s4 out log : Fin U) : Machine U 20 :=
  Composition.machine (stage s0 out log)
    (Composition.machine (stage s1 out log)
      (Composition.machine (stage s2 out log)
        (Composition.machine (stage s3 out log) (stage s4 out log))))

/-- Fuel for the framing pass, in the five actual retained word lengths. -/
def cost (n0 n1 n2 n3 n4 : Nat) : Nat := 4 * (n0 + n1 + n2 + n3 + n4) + 19


end
end SLoad.Frames
