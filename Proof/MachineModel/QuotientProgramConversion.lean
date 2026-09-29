import Proof.MachineModel.BoundedOracleRecoveryProgram

/-!
# The pure-power → quotient-budget conversion (S1, gap7 §3-D4)

Every `PolynomialNatProgram` inhabits the `QuotientNatProgram` carrier at
any target degree carrying two spare polynomial powers per saving power —
universally in the measure, with no onset.  The machine-constructor sites
wrap through `PolynomialNatProgram.toQuotient`; the machine ABI's honest
quotient budget is thereby inhabited by the existing verifiers TODAY, and
the printer body's genuine quotient halts (the R1d ledger) replaces the
wrapped one at machine assembly (S6).

The two interpreter-monotonicity ingredients are in-tree:
`VerifiedLinker.run_fuel_add` and
`BoundedOracleRecoveryProgram.runNPOracleProgram_maximumBits_mono`;
`run_resources_mono` composes them.
-/

namespace NearCubicWires.ExecutableInterfaces

open NearCubicWires
open NearCubicWires.VerifiedLinker
open NearCubicWires.BoundedOracleRecoveryProgram

/-- Successful runs survive enlarging BOTH resource slots. -/
theorem run_resources_mono {program : NPOracleProgram}
    {smallBits largeBits smallFuel largeFuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hbits : smallBits ≤ largeBits) (hfuel : smallFuel ≤ largeFuel)
    (hrun :
      runNPOracleProgram program smallBits smallFuel state = some output) :
    runNPOracleProgram program largeBits largeFuel state = some output := by
  have hwide := runNPOracleProgram_maximumBits_mono hbits hrun
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  exact run_fuel_add hwide extra

/-- One `logScale` power is dominated by two polynomial degrees,
universally in the measure (gap7 §3-D4's spine). -/
theorem logScale_le_sq_succ (m : ℕ) : logScale m ≤ (m + 1) ^ 2 := by
  have h : m + 2 ≤ 2 ^ ((m + 1) ^ 2) := by
    have hlin : m + 2 ≤ 2 ^ (m + 1) := by
      have := Nat.lt_two_pow_self (n := m + 1)
      omega
    have hexp : m + 1 ≤ (m + 1) ^ 2 := by nlinarith
    exact hlin.trans (Nat.pow_le_pow_right (by norm_num) hexp)
  exact Nat.clog_le_of_le_pow h

/-- `c·(m+1)^d ≤ ⌊c·(m+1)^D / L(m)^σ⌋` whenever `d + 2σ ≤ D` —
universally in the measure, no onset. -/
theorem polynomialBudget_le_quotientBudget
    (coefficient degree targetDegree logPower measure : ℕ)
    (hdegree : degree + 2 * logPower ≤ targetDegree) :
    polynomialBudget coefficient degree measure ≤
      quotientBudget coefficient targetDegree logPower measure := by
  have hLpos : 0 < logScale measure ^ logPower :=
    pow_pos (Nat.clog_pos (by norm_num) (by omega)) _
  rw [quotientBudget, Nat.le_div_iff_mul_le hLpos]
  have hsq : logScale measure ^ logPower ≤ (measure + 1) ^ (2 * logPower) := by
    calc logScale measure ^ logPower
        ≤ ((measure + 1) ^ 2) ^ logPower :=
          Nat.pow_le_pow_left (logScale_le_sq_succ _) _
      _ = (measure + 1) ^ (2 * logPower) := by rw [← pow_mul]
  calc polynomialBudget coefficient degree measure *
        logScale measure ^ logPower
      = coefficient * (measure + 1) ^ degree *
          logScale measure ^ logPower := rfl
    _ ≤ coefficient * (measure + 1) ^ degree *
          (measure + 1) ^ (2 * logPower) := Nat.mul_le_mul_left _ hsq
    _ = coefficient * (measure + 1) ^ (degree + 2 * logPower) := by
        rw [pow_add]; ring
    _ ≤ coefficient * (measure + 1) ^ targetDegree :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by omega) hdegree)

/-- **The green-through conversion** (gap7 §3-D4): every pure-power runner
inhabits the quotient carrier at any degree with two spare polynomial
powers per saving power.  Constructor sites wrap through this; the REAL
body's quotient halts (the R1d ledger) replaces the wrapped one at S6. -/
def PolynomialNatProgram.toQuotient {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (targetDegree logPower : ℕ)
    (hdegree : runner.degree + 2 * logPower ≤ targetDegree) :
    QuotientNatProgram Request inputLength requestCode measure where
  program := runner.program
  coefficient := runner.coefficient
  coefficientPositive := runner.coefficientPositive
  degree := targetDegree
  logPower := logPower
  savingFits := by
    intro request
    have hsq : logScale (measure request) ^ logPower ≤
        (measure request + 1) ^ (2 * logPower) := by
      calc logScale (measure request) ^ logPower
          ≤ ((measure request + 1) ^ 2) ^ logPower :=
            Nat.pow_le_pow_left (logScale_le_sq_succ _) _
        _ = (measure request + 1) ^ (2 * logPower) := by rw [← pow_mul]
    have hDeg : (measure request + 1) ^ (2 * logPower) ≤
        (measure request + 1) ^ targetDegree :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hcoeff : (measure request + 1) ^ targetDegree ≤
        runner.coefficient * (measure request + 1) ^ targetDegree :=
      Nat.le_mul_of_pos_left _ runner.coefficientPositive
    exact (hsq.trans hDeg).trans hcoeff
  initialBitsFit := by
    intro request
    exact (runner.initialBitsFit request).trans
      (polynomialBudget_le_quotientBudget runner.coefficient runner.degree
        targetDegree logPower (measure request) hdegree)
  halts := by
    intro request
    obtain ⟨output, houtput⟩ := runner.halts request
    have hle : polynomialBudget runner.coefficient runner.degree
        (measure request) ≤
          quotientBudget runner.coefficient targetDegree logPower
            (measure request) :=
      polynomialBudget_le_quotientBudget runner.coefficient runner.degree
        targetDegree logPower (measure request) hdegree
    exact ⟨output, run_resources_mono hle hle houtput⟩

@[simp] theorem PolynomialNatProgram.toQuotient_degree {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (targetDegree logPower : ℕ)
    (hdegree : runner.degree + 2 * logPower ≤ targetDegree) :
    (runner.toQuotient targetDegree logPower hdegree).degree =
      targetDegree := rfl

@[simp] theorem PolynomialNatProgram.toQuotient_logPower {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (targetDegree logPower : ℕ)
    (hdegree : runner.degree + 2 * logPower ≤ targetDegree) :
    (runner.toQuotient targetDegree logPower hdegree).logPower =
      logPower := rfl

@[simp] theorem PolynomialNatProgram.toQuotient_program {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (targetDegree logPower : ℕ)
    (hdegree : runner.degree + 2 * logPower ≤ targetDegree) :
    (runner.toQuotient targetDegree logPower hdegree).program =
      runner.program := rfl

end NearCubicWires.ExecutableInterfaces
