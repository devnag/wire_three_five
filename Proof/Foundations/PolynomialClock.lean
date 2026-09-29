import Proof.Foundations.ExecutableInterfaces

/-!
# Executable polynomial-dominating refuter clocks

The fixed refuter must dominate the *declared* polynomial budget of its weak
machine for every multiplier.  Iterating the machine's primitive pairing
instruction gives a canonical clock of degree `2^depth`, together with the
program that computes exactly that same value.
-/

namespace NearCubicWires.PolynomialClock

open NearCubicWires
open NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces

theorem natBitLength_le_succ (value : ℕ) :
    natBitLength value ≤ value + 1 := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_le_self 2 value) 1

/-- Repeated self-pairing.  `Nat.pair x x` is at least `x²`, so `depth`
iterations dominate degree `2^depth`. -/
def pairIter : ℕ → ℕ → ℕ
  | 0, value => value
  | depth + 1, value => pairIter depth (Nat.pair value value)

@[simp] theorem pairIter_zero (value : ℕ) : pairIter 0 value = value := rfl

@[simp] theorem pairIter_succ (depth value : ℕ) :
    pairIter (depth + 1) value = pairIter depth (Nat.pair value value) := rfl

theorem value_le_pairIter (depth value : ℕ) :
    value ≤ pairIter depth value := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      exact (Nat.left_le_pair value value).trans (ih (Nat.pair value value))

theorem pairIter_mono_value (depth : ℕ) :
    Monotone (pairIter depth) := by
  intro left right hle
  induction depth generalizing left right with
  | zero => exact hle
  | succ depth ih =>
      apply ih
      calc
        Nat.pair left left ≤ Nat.pair right left := by
          rcases hle.eq_or_lt with h | h
          · simp [h]
          · exact (Nat.pair_lt_pair_left left h).le
        _ ≤ Nat.pair right right := by
          rcases hle.eq_or_lt with h | h
          · simp [h]
          · exact (Nat.pair_lt_pair_right right h).le

theorem pow_twoPow_le_pairIter (depth value : ℕ) :
    value ^ (2 ^ depth) ≤ pairIter depth value := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      calc
        value ^ (2 ^ (depth + 1)) =
            value ^ (2 * (2 ^ depth)) := by
          congr 1
          rw [Nat.pow_succ]
          omega
        _ = (value ^ 2) ^ (2 ^ depth) := by
          rw [pow_mul]
        _ ≤ (Nat.pair value value) ^ (2 ^ depth) := by
          gcongr
          exact (Nat.le_add_right (value ^ 2) value).trans
            (by simpa using Nat.max_sq_add_min_le_pair value value)
        _ ≤ pairIter depth (Nat.pair value value) := ih _
        _ = pairIter (depth + 1) value := rfl

theorem pairIter_add_one_le_pow (depth value : ℕ) :
    pairIter depth value + 1 ≤ (value + 1) ^ (2 ^ depth) := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      have hpair :
          Nat.pair value value + 1 ≤ (value + 1) ^ 2 := by
        exact Nat.succ_le_iff.mpr <| by
          simpa using Nat.pair_lt_max_add_one_sq value value
      calc
        pairIter (depth + 1) value + 1 =
            pairIter depth (Nat.pair value value) + 1 := rfl
        _ ≤ (Nat.pair value value + 1) ^ (2 ^ depth) := ih _
        _ ≤ ((value + 1) ^ 2) ^ (2 ^ depth) :=
          Nat.pow_le_pow_left hpair (2 ^ depth)
        _ = (value + 1) ^ (2 ^ (depth + 1)) := by
          rw [← pow_mul]
          congr 1
          rw [Nat.pow_succ]
          omega

/-- The canonical refuter clock at source length `n`. -/
def pairClock (depth n : ℕ) : ℕ :=
  pairIter depth n

theorem pow_twoPow_le_pairClock (depth n : ℕ) :
    n ^ (2 ^ depth) ≤ pairClock depth n :=
  pow_twoPow_le_pairIter depth n

theorem pairClock_polynomiallyBounded (depth : ℕ) :
    PolynomiallyBounded (pairClock depth) := by
  refine ⟨1, 2 ^ depth, by omega, ?_⟩
  intro n
  simpa [pairClock] using
    (Nat.le_add_right (pairIter depth n) 1).trans
      (pairIter_add_one_le_pow depth n)

def pairTail : ℕ → ℕ → NPOracleProgram
  | _pc, 0 => [.halt 0]
  | pc, depth + 1 =>
      .pair 0 0 0 (pc + 1) :: pairTail (pc + 1) depth

@[simp] theorem pairTail_length (pc depth : ℕ) :
    (pairTail pc depth).length = depth + 1 := by
  induction depth generalizing pc with
  | zero => simp [pairTail]
  | succ depth ih => simp [pairTail, ih]

theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-- Execute a self-pairing suffix after an arbitrary already-executed prefix.
This prefix-general statement is what makes absolute program counters explicit
and prevents an unverified "run the remaining list" shortcut. -/
theorem run_pairTail (prelude : NPOracleProgram) (depth maximumBits extra : ℕ)
    (state : NPOracleState) (value : ℕ)
    (hpc : state.pc = prelude.length)
    (hvalue : state.registers 0 = value)
    (hbits : natBitLength (pairIter depth value) ≤ maximumBits) :
    runNPOracleProgram (prelude ++ pairTail prelude.length depth)
        maximumBits (extra + depth + 1) state =
      some (pairIter depth value) := by
  induction depth generalizing prelude state value with
  | zero =>
      have hvalueBits : natBitLength value ≤ maximumBits := by
        simpa [pairIter] using hbits
      simp [pairTail, runNPOracleProgram, hpc, hvalue, hvalueBits]
  | succ depth ih =>
      have hnext :
          Nat.pair value value ≤
            pairIter depth (Nat.pair value value) :=
        value_le_pairIter depth (Nat.pair value value)
      have hpairBits :
          natBitLength (Nat.pair value value) ≤ maximumBits :=
        (natBitLength_mono hnext).trans hbits
      let instruction : NPOracleInstruction :=
        .pair 0 0 0 (prelude.length + 1)
      let nextState :=
        (state.write 0 (Nat.pair value value)).jump (prelude.length + 1)
      have hstep :
          runNPOracleProgram
              (prelude ++ pairTail prelude.length (depth + 1))
              maximumBits (extra + (depth + 1) + 1) state =
            runNPOracleProgram
              ((prelude ++ [instruction]) ++
                pairTail (prelude.length + 1) depth)
              maximumBits (extra + depth + 1) nextState := by
        simp only [pairTail, runNPOracleProgram]
        simp [hpc, hvalue, instruction, nextState, NPOracleState.boundedWrite,
          hpairBits, List.append_assoc]
      rw [hstep]
      have hrun := ih (prelude ++ [instruction]) nextState
        (Nat.pair value value)
        (by
          simp [nextState, NPOracleState.jump])
        (by
          simp [nextState, NPOracleState.jump, NPOracleState.write])
        hbits
      simpa [pairIter] using hrun

theorem pairTail_oracleFree (pc depth : ℕ) :
    OracleFree (pairTail pc depth) := by
  induction depth generalizing pc with
  | zero => simp [OracleFree, pairTail]
  | succ depth ih =>
      simp only [pairTail, OracleFree, List.all_cons, Bool.true_and]
      simpa only [OracleFree] using ih (pc + 1)

/-- A kernel-checked clock witness whose reported value is computed by the
same self-pairing program used in its growth proof. -/
def pairClockTimeConstructible (depth : ℕ) :
    TimeConstructible (pairClock depth) where
  program := pairTail 0 depth
  coefficient := depth + 1
  coefficientPositive := by omega
  oracleFree := pairTail_oracleFree 0 depth
  computesBound := by
    intro n
    let clock := pairClock depth n
    let budget := (depth + 1) * (clock + 1)
    have hminimum : depth + 1 ≤ budget := by
      dsimp [budget]
      nlinarith
    obtain ⟨extra, hbudget⟩ := Nat.exists_eq_add_of_le hminimum
    have hbits : natBitLength clock ≤ budget := by
      calc
        natBitLength clock ≤ clock + 1 := natBitLength_le_succ clock
        _ ≤ budget := by
          dsimp [budget]
          nlinarith
    have hrun := run_pairTail ([] : NPOracleProgram) depth budget extra
      (initialNPOracleState n n) n
      (by simp [initialNPOracleState])
      (by simp [initialNPOracleState])
      (by simpa [clock, pairClock] using hbits)
    have hfuel : budget = extra + depth + 1 := by
      omega
    change
      runNPOracleProgram (pairTail 0 depth) budget budget
        (initialNPOracleState n n) =
          some clock
    rw [hfuel] at hrun
    rw [hfuel]
    simpa [clock, pairClock] using hrun

end NearCubicWires.PolynomialClock
