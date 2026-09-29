import Proof.Circuits.BoundedOracleStructuralFormulaTable

/-!
# Selective bounded-oracle structural compiler

The canonical verifier compiler is append-only.  A pointwise formula emitter
therefore does not need to retain its exponentially large node suffix: it need
only count emitted nodes, remember the node at one requested offset, and retain
the live wire indices required by later compiler steps.  The definitions below
are the proof-level transition system for that streaming implementation.  They
mirror the sole `BooleanDAGBuilder` compiler operation-for-operation; no second
gate grammar or CNF schedule is introduced.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveCompiler

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

/-! ## Refinement to the sole append-only builder -/

@[simp] private theorem compiledWire_live_output {n : ℕ}
    {prior : BooleanDAGBuilder n} {function : BoolFunction n}
    (wire : CompiledWire prior function) :
    wire.live.output = wire.output :=
  rfl

@[simp] private theorem liveWire_lift_output_val {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (wire : LiveWire prior) :
    (wire.lift extension).output.val = wire.output.val :=
  rfl

/-! The selected offset is immutable compiler context.  Keeping this as a
separate invariant avoids storing it redundantly in every wire relation. -/

end NearCubicWires.BoundedOracleStructuralSelectiveCompiler
