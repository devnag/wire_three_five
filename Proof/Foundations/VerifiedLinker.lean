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

theorem boundedWrite_bits_mono
    {state nextState : NPOracleState} {oldBits newBits register value : ℕ}
    (hexec : state.boundedWrite oldBits register value = some nextState)
    (hbits : oldBits ≤ newBits) :
    state.boundedWrite newBits register value = some nextState := by
  simp only [NPOracleState.boundedWrite] at hexec ⊢
  split at hexec
  · rename_i hold
    simp only [Option.some.injEq] at hexec
    subst nextState
    simp [le_trans hold hbits]
  · simp at hexec

def instructionRegisters : NPOracleInstruction → List ℕ
  | .halt output => [output]
  | .set register _ _ => [register]
  | .copy source destination _ => [source, destination]
  | .increment register _ => [register]
  | .decrement register _ => [register]
  | .add left right destination _ => [left, right, destination]
  | .subtract left right destination _ => [left, right, destination]
  | .pair left right destination _ => [left, right, destination]
  | .unpairLeft source destination _ => [source, destination]
  | .unpairRight source destination _ => [source, destination]
  | .branchZero register _ _ => [register]
  | .encodeNat source destination _ => [source, destination]
  | .shiftRight source _ destination _ => [source, destination]
  | .shiftLeft source _ destination _ => [source, destination]
  | .testBit source index destination _ => [source, index, destination]
  | .sat query destination _ => [query, destination]

def instructionRegisterSpan (instruction : NPOracleInstruction) : ℕ :=
  (instructionRegisters instruction).foldr max 0 + 1

def programRegisterSpan : NPOracleProgram → ℕ
  | [] => 2
  | instruction :: rest =>
      max (instructionRegisterSpan instruction) (programRegisterSpan rest)

structure LinkLayout where
  firstSpan : ℕ
  secondSpan : ℕ
  firstBase : ℕ
  resetBase : ℕ
  secondBase : ℕ
  secondRegisterBase : ℕ
  savedLengthRegister : ℕ
  transferRegister : ℕ

def relocateState (pcOffset registerOffset : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) : NPOracleState where
  pc := pcOffset + state.pc
  registers := fun candidate =>
    if registerOffset ≤ candidate then
      state.registers (candidate - registerOffset)
    else lowerRegisters candidate

@[simp] theorem relocateState_pc (pcOffset registerOffset : ℕ)
    (lowerRegisters : ℕ → ℕ) (state : NPOracleState) :
    (relocateState pcOffset registerOffset lowerRegisters state).pc =
      pcOffset + state.pc := rfl

def firstStageState (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) : NPOracleState where
  pc := layout.firstBase + state.pc
  registers := fun candidate =>
    if candidate < layout.firstSpan then state.registers candidate
    else if candidate = layout.savedLengthRegister then inputLength else 0

@[simp] theorem firstStageState_pc (layout : LinkLayout) (inputLength : ℕ)
    (state : NPOracleState) :
    (firstStageState layout inputLength state).pc =
      layout.firstBase + state.pc := rfl

theorem run_fuel_add {program : NPOracleProgram} {maximumBits fuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hexec :
      runNPOracleProgram program maximumBits fuel state = some output)
    (extra : ℕ) :
    runNPOracleProgram program maximumBits (fuel + extra) state = some output := by
  induction fuel generalizing state with
  | zero => simp [runNPOracleProgram] at hexec
  | succ fuel ih =>
      rw [Nat.succ_add]
      cases hlookup : program[state.pc]? with
      | none =>
          simp [runNPOracleProgram, hlookup] at hexec
      | some instruction =>
          simp only [runNPOracleProgram, hlookup] at hexec ⊢
          cases instruction with
          | halt _ =>
              exact hexec
          | set register value _ =>
              cases hwrite :
                  state.boundedWrite maximumBits register value with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | copy source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers source) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | increment register _ =>
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register + 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | decrement register _ =>
              simp only at hexec ⊢
              rw [Nat.pred_eq_sub_one] at hexec ⊢
              cases hwrite : state.boundedWrite maximumBits register
                  (state.registers register - 1) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | add left right destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left + state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | subtract left right destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (state.registers left - state.registers right) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | pair left right destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.pair (state.registers left)
                    (state.registers right)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | unpairLeft source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers source)).1 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | unpairRight source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (Nat.unpair (state.registers source)).2 with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | branchZero _ _ _ =>
              exact ih hexec
          | encodeNat source destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (CanonicalBinary.encodeNat
                    (state.registers source)) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | shiftRight source amount destination _ =>
              simp only at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                exact ih hexec
          | shiftLeft source amount destination _ =>
              simp only at hexec ⊢
              split at hexec
              · simp at hexec
              · rename_i nextState hwrite
                exact ih hexec
          | testBit source index destination _ =>
              cases hwrite : state.boundedWrite maximumBits destination
                  (((state.registers source).testBit
                    (state.registers index)).toNat) with
              | none => simp [hwrite] at hexec
              | some nextState =>
                  simp only [hwrite] at hexec ⊢
                  exact ih hexec
          | sat query destination _ =>
              by_cases hquery :
                  natBitLength (state.registers query) ≤ maximumBits
              · simp only [if_pos hquery] at hexec ⊢
                cases hwrite : state.boundedWrite maximumBits destination
                    (encodedSat (state.registers query)).toNat with
                | none => simp [hwrite] at hexec
                | some nextState =>
                    simp only [hwrite] at hexec ⊢
                    exact ih hexec
              · simp [hquery] at hexec

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
