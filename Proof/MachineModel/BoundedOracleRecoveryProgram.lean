import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Executable bounded-oracle recovery

This module owns the public request syntax and the fixed-program boundary for
Appendix C.12 recovery.  Requests contain only the original input, the circuit
bound, and the requested description coordinate.  In particular, no circuit,
CNF, SAT answer, semantic verifier, or recovery callback is accepted as input.

The structural-CNF controller is intentionally assembled from the published
fixed PCP runners and the shared `DynamicCNFBuilder`/zero-first SAT reducer.
Keeping the request codec here makes that trust boundary independently
auditable before the larger linked controller is introduced below.
-/

namespace NearCubicWires.BoundedOracleRecoveryProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed request-normalization prefix -/

/-! ## Shared resource widening -/

private theorem boundedWrite_mono
    {state nextState : NPOracleState}
    {smallBits largeBits register value : ℕ}
    (hbits : smallBits ≤ largeBits)
    (hwrite :
      state.boundedWrite smallBits register value = some nextState) :
    state.boundedWrite largeBits register value = some nextState :=
  VerifiedLinker.boundedWrite_bits_mono hwrite hbits

/-- Successful executions are stable when the register-width envelope is
widened.  This is the resource analogue of `run_fuel_add`; linked stages can
therefore share one maximum without reproving their instruction traces. -/
theorem runNPOracleProgram_maximumBits_mono
    {program : NPOracleProgram} {smallBits largeBits fuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hbits : smallBits ≤ largeBits)
    (hrun :
      runNPOracleProgram program smallBits fuel state = some output) :
    runNPOracleProgram program largeBits fuel state = some output := by
  induction fuel generalizing state with
  | zero =>
      simp [runNPOracleProgram] at hrun
  | succ fuel ih =>
      cases hlookup : program[state.pc]? with
      | none =>
          simp [runNPOracleProgram, hlookup] at hrun
      | some instruction =>
          cases instruction with
          | halt outputRegister =>
              by_cases hsmall :
                  natBitLength (state.registers outputRegister) ≤ smallBits
              · have hlarge := hsmall.trans hbits
                simp only [runNPOracleProgram, hlookup] at hrun ⊢
                rw [if_pos hsmall] at hrun
                rw [if_pos hlarge]
                exact hrun
              · simp only [runNPOracleProgram, hlookup] at hrun
                rw [if_neg hsmall] at hrun
                contradiction
          | set register value next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits register value with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | copy source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (state.registers source) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | increment register next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits register
                    (state.registers register + 1) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | decrement register next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              rw [Nat.pred_eq_sub_one] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits register
                    (state.registers register - 1) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | add left right destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (state.registers left + state.registers right) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | subtract left right destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (state.registers left - state.registers right) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | pair left right destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.pair (state.registers left)
                      (state.registers right)) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | unpairLeft source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.unpair (state.registers source)).1 with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | unpairRight source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.unpair (state.registers source)).2 with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | branchZero register zeroTarget nonzeroTarget =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              exact ih hrun
          | encodeNat source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (encodeNat (state.registers source)) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | shiftRight source amount destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.shiftRight (state.registers source) amount) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  rw [hwrite] at hrun
                  exact ih hrun
          | shiftLeft source amount destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.shiftLeft (state.registers source) amount) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  rw [hwrite] at hrun
                  exact ih hrun
          | testBit source index destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (((state.registers source).testBit
                      (state.registers index)).toNat) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  rw [hwrite] at hrun
                  exact ih hrun
          | sat queryRegister destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              by_cases hquery :
                  natBitLength (state.registers queryRegister) ≤ smallBits
              · rw [if_pos (hquery.trans hbits)]
                rw [if_pos hquery] at hrun
                cases hwrite :
                    state.boundedWrite smallBits destination
                      (encodedSat
                        (state.registers queryRegister)).toNat with
                | none =>
                    simp [hwrite] at hrun
                | some nextState =>
                    rw [boundedWrite_mono hbits hwrite]
                    exact ih (by simpa [hwrite] using hrun)
              · rw [if_neg hquery] at hrun
                contradiction

/-! ## CNF stream to zero-first input -/

/-! ## Forward raw triples to the canonical prefix-SAT input -/

end NearCubicWires.BoundedOracleRecoveryProgram
