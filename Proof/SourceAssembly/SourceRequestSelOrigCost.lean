import Proof.SourceAssembly.SourceRequestSymOriginal
import Proof.Circuits.DecompositionSourceRealization

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics ExecutableInterfaces
noncomputable section
namespace NearCubicWires.SourceRequest.SelOrigCost
open PCJd4d1d9d7d1fa4313_Production

/-! ## Powers of `S + 1` -/

theorem lin_le (S E : Nat) (hE : 1 ≤ E) : S + 1 ≤ (S + 1) ^ E := by
  have h := Nat.pow_le_pow_right (show 0 < S + 1 by omega) hE
  rw [pow_one] at h
  exact h

/-- The writer's fuel is quadratic in `S`. -/
theorem wFuel_le (P q N S : Nat) (hP : P ≤ S) (hq : q ≤ S) (hN : N ≤ S) :
    1 + 1 + CloseoutRowsSupportStream.circuitBudget P q N ≤ 6002 * (S + 1) ^ 2 := by
  unfold CloseoutRowsSupportStream.circuitBudget
  have h1 : (N + 2) * (P + q + 1) ≤ (S + 2) * (2 * S + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (S + 2) * (2 * S + 1) + (S * S + S + 1) = 3 * (S + 1) ^ 2 := by ring
  have e2 : 2000 * (N + 2) * (P + q + 1) = 2000 * ((N + 2) * (P + q + 1)) := by ring
  have h2 : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ## The THR original factor -/

/-- The THR original factor's coefficient. -/
def thrOC (a : DecompositionAlgorithm) : Nat := 3000 * (a.coefficient + 2) ^ 2 + 30000

/-- The THR original factor's exponent. -/
def thrOE (a : DecompositionAlgorithm) : Nat := 2 * a.degree + 2

/-- The decomposition entry's budget at the retained top gate. -/
theorem entry_le (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) (S : Nat)
    (hr : r.arity + r.gate.encodingBits + 1 ≤ S + 1) :
    DecompositionSource.Entry.budget a r ≤ 1024 * ((a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a) := by
  have h := DecompositionSource.entry_budget_coarse a r
  have hsb : DecompositionSource.sourceBudget a r ≤ a.coefficient * (S + 1) ^ (a.degree + 1) := by
    unfold DecompositionSource.sourceBudget
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hr _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hpar : DecompositionSource.parameter r + 1 ≤ 2 * (S + 1) ^ (a.degree + 1) := by
    unfold DecompositionSource.parameter
    have := lin_le S (a.degree + 1) (by omega)
    omega
  have hB : DecompositionSource.sourceBudget a r + DecompositionSource.parameter r + 1 ≤
      (a.coefficient + 2) * (S + 1) ^ (a.degree + 1) := by
    rw [Nat.add_mul]; omega
  have hsq := Nat.pow_le_pow_left hB 2
  have e : ((a.coefficient + 2) * (S + 1) ^ (a.degree + 1)) ^ 2 = (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a := by
    unfold thrOE; rw [mul_pow, ← pow_mul]; ring_nf
  rw [e] at hsq
  omega

/-- The decomposition entry's output word. -/
theorem output_le (a : DecompositionAlgorithm) (r : ExactDecompositionRequest) (S : Nat)
    (hr : r.arity + r.gate.encodingBits + 1 ≤ S + 1) (hn : 2 * natBitLength r.arity + 1 ≤ S + 1) :
    (DecompositionSource.Entry.output a r).length ≤ (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a := by
  unfold DecompositionSource.Entry.output
  rw [List.length_append, DecompositionSource.natWord_length]
  have ho := DecompositionSource.output_length a r
  have hsb : DecompositionSource.sourceBudget a r ≤ a.coefficient * (S + 1) ^ thrOE a := by
    unfold DecompositionSource.sourceBudget thrOE
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hr _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hl := lin_le S (thrOE a) (by unfold thrOE; omega)
  have hc : a.coefficient + 1 ≤ (a.coefficient + 2) ^ 2 := by nlinarith
  have hm : (a.coefficient + 1) * (S + 1) ^ thrOE a ≤ (a.coefficient + 2) ^ 2 * (S + 1) ^ thrOE a := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul, one_mul] at hm
  omega

/-! ## The SYM original factor -/

end NearCubicWires.SourceRequest.SelOrigCost
end

