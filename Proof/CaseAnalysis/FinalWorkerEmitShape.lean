import Proof.CaseAnalysis.FinalWorkerDockBody
import Proof.Amplification.RecoveryTapeSupport

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A local run never shortens a tape -/

/-! ## §2 The answer slots are outside both docked stages -/

theorem answerSlot_ne_entrySlot (k : Fin 90) (j : Fin 29) : entrySlot k ≠ answerSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [entrySlot_val, answerSlot_val] at hv
  have := k.isLt
  omega

theorem answerSlot_ne_foldSlot (k : Fin 95) (j : Fin 29) : foldSlot k ≠ answerSlot j := by
  intro h
  have hv := congrArg Fin.val h
  rw [foldSlot_val, answerSlot_val] at hv
  have := k.isLt
  split at hv <;> omega

/-! ## §3 The premise really is satisfiable -/

/-! ## §4 The current `hemit` is refutable -/

/-! ## §5 The corrected premise -/

/-- The emitter's `n`-determined constant ports: the runtime width word and the
two normalization fields.  These are the loader's, not the emit loader's: they
name no fold output. -/
def emitConstants (b : ℕ) (j : Fin 29) : List Bool :=
  if j.val = 0 then List.replicate b true
  else if j.val = 26 ∨ j.val = 27 then frame (binary b 1) else []

/-- **What the loader must leave on bank tapes `187 .. 215`.**  The three data
ports `23, 24, 25` are empty -- the emit loader writes them from the fold's
stored accumulator -- and the constant ports carry their words. -/
def EmitEntry (b : ℕ) (bank : Fin 218 → List Bool) : Prop :=
  ∀ j : Fin 29,
    bank (answerSlot j) = if j.val = 23 ∨ j.val = 24 ∨ j.val = 25 then [] else emitConstants b j

/-- **The corrected premise plus the three data ports is exactly
`Append.input`.**  Nothing else has to be written, and nothing has to be
erased. -/
theorem emitEntry_append (b : ℕ) (q : CompetitorValidity.Estimate)
    (bank : Fin 218 → List Bool) (hentry : EmitEntry b bank)
    (out : Fin 218 → List Bool)
    (h23 : out (answerSlot 23) = frame (binary (CompetitorRationalDecision.width b) q.positive))
    (h24 : out (answerSlot 24) = frame (binary (CompetitorRationalDecision.width b) q.negative))
    (h25 : out (answerSlot 25) = frame (binary (CompetitorRationalDecision.width b) q.denominator))
    (hrest : ∀ j : Fin 29, ¬ (j.val = 23 ∨ j.val = 24 ∨ j.val = 25) →
      out (answerSlot j) = bank (answerSlot j)) (j : Fin 29) :
    out (answerSlot j) = CloseoutRowsEstimatorCoefficients.Append.input b q 1 1 j := by
  by_cases hj : j.val = 23 ∨ j.val = 24 ∨ j.val = 25
  · have hje : j = 23 ∨ j = 24 ∨ j = 25 := by
      rcases hj with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    rcases hje with rfl | rfl | rfl
    · exact h23
    · exact h24
    · exact h25
  · rw [hrest j hj, hentry j, if_neg hj]
    have hv : j.val ≠ 23 ∧ j.val ≠ 24 ∧ j.val ≠ 25 := by
      refine ⟨fun h => hj (Or.inl h), fun h => hj (Or.inr (Or.inl h)), fun h => hj (Or.inr (Or.inr h))⟩
    unfold emitConstants CloseoutRowsEstimatorCoefficients.Append.input
    by_cases h0 : j.val = 0
    · rw [if_pos h0, if_pos (Fin.ext h0 : j = 0)]
    · rw [if_neg h0, if_neg (fun h : j = 0 => h0 (congrArg Fin.val h))]
      by_cases h26 : j.val = 26 ∨ j.val = 27
      · rw [if_pos h26, if_pos (by omega : 23 ≤ j.val ∧ j.val ≤ 27)]
        rcases h26 with h | h
        · unfold CloseoutRowsEstimatorCoefficients.Append.scalarFields
          rw [show j = (26 : Fin 29) from Fin.ext h]
          rfl
        · unfold CloseoutRowsEstimatorCoefficients.Append.scalarFields
          rw [show j = (27 : Fin 29) from Fin.ext h]
          rfl
      · rw [if_neg h26, if_neg (by omega : ¬ (23 ≤ j.val ∧ j.val ≤ 27))]

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
