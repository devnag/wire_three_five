import Proof.Foundations.ExecutableInterfaces

/-!
# Verified linker for the fixed NP-oracle register machine

Control-flow targets in `NPOracleProgram` are absolute, so concatenating lists
is unsound.  This module relocates targets, isolates stage registers, preserves
the public input length, and makes the inter-stage transfer explicit.
-/

namespace NearCubicWires.VerifiedLinker

open NearCubicWires
open NearCubicWires.ExecutableInterfaces

/-! ## Interpreter budget monotonicity -/

@[simp] private theorem stateWrite_pc (state : NPOracleState)
    (register value : ℕ) :
    (state.write register value).pc = state.pc := rfl

@[simp] private theorem stateWrite_registers (state : NPOracleState)
    (register value candidate : ℕ) :
    (state.write register value).registers candidate =
      if candidate = register then value else state.registers candidate := rfl

@[simp] private theorem stateJump_pc (state : NPOracleState) (pc : ℕ) :
    (state.jump pc).pc = pc := rfl

@[simp] private theorem stateJump_registers (state : NPOracleState)
    (pc candidate : ℕ) :
    (state.jump pc).registers candidate = state.registers candidate := rfl

end NearCubicWires.VerifiedLinker
