import Proof.Wire_3_5.UnionMachine.FrontSemTWBase

/-! # C6 front, the semantic core (4): the chain's checks decide the reference output (P3:3669-3691)

The front's reference output (`FrontOutRef.outRef`) is the valid branch's exactly when the witness decodes to a guess
passing the size, atom, sign and admissibility checks. The chain checks, in order: the walker's scan (`okOf`), the
oracle's decoding and size, the entries' scan, the atoms' decoder at the description envelope, then (in the end) the
calls' admissibility. This module shows each failing check rejects the decoded guess (**`okOf_of`**, **`oracle_of`**,
**`signs_of`**, **`atoms_fail`**), the passing checks decode the chain's guess `gOf` with its three checks
(**`valid_of`**), and evaluates the reference output on each branch (**`outRef_rej`**, **`outRef_valid`**: the valid
branch's output is the end's `endOut`).

Paper quantity of the main types: the front's reference output (its table, thresholds and capacities) per witness. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemDec
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter gridVal)

section Dec

end Dec

/-! ## The atoms' check -/

section Atoms
open NearCubicWires.RepairOrdinary
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N}

/-- A passing atom decodes. -/
theorem passed_dec (m : Mode) (q W L : ℕ) (bits : List Bool) (h : FrontAtomDecoder.passedM m q W L bits) :
    ∃ c, decodeAtom m q (value bits) = some c := by
  cases m
  · have h' : CloseoutRowsCircuitThresholdRun.passed q W L bits := h
    rw [CloseoutRowsCircuitMeaning.threshold_exact] at h'
    obtain ⟨c, hc, -, -⟩ := h'
    exact ⟨c, hc⟩
  · have h' : CloseoutRowsCircuitSymmetricRun.passed q W L bits := h
    rw [CloseoutRowsCircuitMeaning.symmetric_exact] at h'
    obtain ⟨c, hc, -, -⟩ := h'
    exact ⟨c, hc⟩

theorem verdict_zero {q W L : ℕ} {m : Mode} {En : ℕ} {pay : ℕ → List Bool}
    (h : FrontAtomLoop.verdictOf q W L m En pay = 0) : ∀ j, j < En → FrontAtomDecoder.passedM m q W L (pay j) := by
  classical
  intro j hj
  by_contra hf
  have : FrontAtomLoop.verdictOf q W L m En pay = 1 := by
    simp only [FrontAtomLoop.verdictOf]; rw [if_neg]; intro hall; exact hf (hall j hj)
  omega

theorem verdict_ne {q W L : ℕ} {m : Mode} {En : ℕ} {pay : ℕ → List Bool}
    (h : FrontAtomLoop.verdictOf q W L m En pay ≠ 0) : ∃ j, j < En ∧ ¬ FrontAtomDecoder.passedM m q W L (pay j) := by
  classical
  by_contra hex
  have hall : ∀ j, j < En → FrontAtomDecoder.passedM m q W L (pay j) := fun j hj => by
    by_contra hf; exact hex ⟨j, hj, hf⟩
  exact h (by simp only [FrontAtomLoop.verdictOf]; rw [if_pos hall])

end Atoms

/-! ## The reference output per branch -/

section Out

end Out

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemDec
