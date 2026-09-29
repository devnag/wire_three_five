import Proof.CaseAnalysis.FinalTailFeedPrep

/-! **Decision tail, stage 2b-ii — feed one comparator from one phase's record.**

Paper C.10: for one estimated real, one test. The phase's estimate sits as one
record word on its scratch slot. Thirteen docked stages lay the comparator's
input and run it, and `compare_step` reads the verdict.

The record is `recordWord (w W) est 1 1`, so its numerator fields already carry
`binary (w2 W)`; the comparator therefore runs at parameter `b := w2 W`, whose
numerator tapes want `binary (w3 W)` and whose denominator tapes want
`binary (w2 W)`. Hence: the estimate's denominator is lifted out of the record
and used verbatim, its positive and negative parts are lifted and widened one
`width` through their own normaliser blocks, and the threshold's numerator and
denominator, the literal `0` and the unary width driver are written as literals.

Every stage that WRITES a tape through `Field.machine` leaves that tape's head
past the copy, while `compare_step` demands head `0` on its whole block; the
paid head reset `CompetitorRecordRewind.rewind_run` is docked after each such
copy, driven by the comparator's own unary tape and logging into a spare slot.
Literal and normaliser stages return the head function unchanged, so no other
reset is needed.

Every stage is an existing GREEN machine docked by an injective slot map; this
module is only their `Step.seq`. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeed

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorMonomialStream
open CompetitorThresholdDecision SignedSortKey ClockNormalize
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockField
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockCmp
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep (w w2 Parked)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ### Widths -/

/-! ### Three- and five-tape docking maps -/

/-- A three-tape docking map. -/
def triSlots (a b c : Fin bank) (i : Fin 3) : Fin bank :=
  if i.val = 0 then a else if i.val = 1 then b else c

theorem triSlots_injective (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (triSlots a b c) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (show a = b from h) hab
  · exact absurd (show a = c from h) hac
  · exact absurd (show b = a from h).symm hab
  · rfl
  · exact absurd (show b = c from h) hbc
  · exact absurd (show c = a from h).symm hac
  · exact absurd (show c = b from h).symm hbc
  · rfl

/-- A five-tape docking map. -/
def quintSlots (a b c d e : Fin bank) (i : Fin 5) : Fin bank :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c
  else if i.val = 3 then d else e

theorem quintSlots_injective (a b c d e : Fin bank)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective (quintSlots a b c d e) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (show a = b from h) hab
  · exact absurd (show a = c from h) hac
  · exact absurd (show a = d from h) had
  · exact absurd (show a = e from h) hae
  · exact absurd (show b = a from h).symm hab
  · rfl
  · exact absurd (show b = c from h) hbc
  · exact absurd (show b = d from h) hbd
  · exact absurd (show b = e from h) hbe
  · exact absurd (show c = a from h).symm hac
  · exact absurd (show c = b from h).symm hbc
  · rfl
  · exact absurd (show c = d from h) hcd
  · exact absurd (show c = e from h) hce
  · exact absurd (show d = a from h).symm had
  · exact absurd (show d = b from h).symm hbd
  · exact absurd (show d = c from h).symm hcd
  · rfl
  · exact absurd (show d = e from h) hde
  · exact absurd (show e = a from h).symm hae
  · exact absurd (show e = b from h).symm hbe
  · exact absurd (show e = c from h).symm hce
  · exact absurd (show e = d from h).symm hde
  · rfl

/-! ### Port projections of the two-tape and three-tape docks -/

theorem pairA0 (src dst : Fin bank) (hne : src ≠ dst) (A : Fin bank → List Bool)
    (v : Fin 2 → List Bool) : install (pairSlots src dst) A v src = v 0 :=
  install_slot (pairSlots src dst) (pairSlots_injective src dst hne) A v 0

theorem pairA1 (src dst : Fin bank) (hne : src ≠ dst) (A : Fin bank → List Bool)
    (v : Fin 2 → List Bool) : install (pairSlots src dst) A v dst = v 1 :=
  install_slot (pairSlots src dst) (pairSlots_injective src dst hne) A v 1

theorem pairAout (src dst : Fin bank) (A : Fin bank → List Bool) (v : Fin 2 → List Bool)
    (i : Fin bank) (h0 : src ≠ i) (h1 : dst ≠ i) :
    install (pairSlots src dst) A v i = A i := by
  refine install_other (pairSlots src dst) A v i ?_
  intro j
  fin_cases j
  · exact h0
  · exact h1

theorem pairH0 (src dst : Fin bank) (hne : src ≠ dst) (H : Fin bank → ℕ) (v : Fin 2 → ℕ) :
    dockH (pairSlots src dst) H v src = v 0 :=
  dockH_slot (pairSlots src dst) (pairSlots_injective src dst hne) H v 0

theorem pairH1 (src dst : Fin bank) (hne : src ≠ dst) (H : Fin bank → ℕ) (v : Fin 2 → ℕ) :
    dockH (pairSlots src dst) H v dst = v 1 :=
  dockH_slot (pairSlots src dst) (pairSlots_injective src dst hne) H v 1

theorem pairHout (src dst : Fin bank) (H : Fin bank → ℕ) (v : Fin 2 → ℕ)
    (i : Fin bank) (h0 : src ≠ i) (h1 : dst ≠ i) :
    dockH (pairSlots src dst) H v i = H i := by
  refine dockH_other (pairSlots src dst) H v i ?_
  intro j
  fin_cases j
  · exact h0
  · exact h1

theorem triA0 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (A : Fin bank → List Bool) (v : Fin 3 → List Bool) :
    install (triSlots a b c) A v a = v 0 :=
  install_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) A v 0

theorem triA1 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (A : Fin bank → List Bool) (v : Fin 3 → List Bool) :
    install (triSlots a b c) A v b = v 1 :=
  install_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) A v 1

theorem triAout (a b c : Fin bank) (A : Fin bank → List Bool) (v : Fin 3 → List Bool)
    (i : Fin bank) (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    install (triSlots a b c) A v i = A i := by
  refine install_other (triSlots a b c) A v i ?_
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc

theorem triH0 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (H : Fin bank → ℕ) (v : Fin 3 → ℕ) : dockH (triSlots a b c) H v a = v 0 :=
  dockH_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) H v 0

theorem triH1 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (H : Fin bank → ℕ) (v : Fin 3 → ℕ) : dockH (triSlots a b c) H v b = v 1 :=
  dockH_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) H v 1

theorem triHout (a b c : Fin bank) (H : Fin bank → ℕ) (v : Fin 3 → ℕ)
    (i : Fin bank) (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    dockH (triSlots a b c) H v i = H i := by
  refine dockH_other (triSlots a b c) H v i ?_
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc

/-! ### The five stage forms, each stated by PORT PROJECTION -/

/-- One paid head reset, raw: the record rewinder walks the head on tape `0` back
to `0` against a unary driver of length `C`, changing no word. -/
theorem rewind_base (source : List Bool) (C pos : ℕ) (hpos : pos ≤ C) :
    Step CompetitorRecordRewind.machine (2*C+2)
      ![pos, 0, 0] ![source, List.replicate C true, []]
      ![0, 0, 0] ![source, List.replicate C true, List.replicate C false] := by
  obtain ⟨r, hr, hf, _⟩ := CompetitorRecordRewind.rewind_run source C pos hpos
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hf]
    rfl
  · rw [hf]
    rfl

/-! ### The three record fields the comparator needs, and their cursors -/



/-! ### The seven comparator input tapes -/

theorem posSlot_lt (lower : Bool) : (posSlot lower).val < 7 := by cases lower <;> decide
theorem negSlot_lt (lower : Bool) : (negSlot lower).val < 7 := by cases lower <;> decide
theorem qnumSlot_lt (lower : Bool) : (qnumSlot lower).val < 7 := by cases lower <;> decide
theorem zeroSlot_lt (lower : Bool) : (zeroSlot lower).val < 7 := by cases lower <;> decide
theorem denSlot_lt (lower : Bool) : (denSlot lower).val < 7 := by cases lower <;> decide
theorem qdenSlot_lt (lower : Bool) : (qdenSlot lower).val < 7 := by cases lower <;> decide

/-- Below `7` the comparator's block is exactly its six operands and its driver. -/
theorem slot_cover (lower : Bool) (j : Fin 67) (hj : j.val < 7) :
    j = posSlot lower ∨ j = negSlot lower ∨ j = qnumSlot lower ∨ j = zeroSlot lower ∨
      j = denSlot lower ∨ j = qdenSlot lower ∨ j = 6 := by
  have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨
      j.val = 6 := by omega
  cases lower
  · rcases h with h|h|h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))))
  · rcases h with h|h|h|h|h|h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))))


end
end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeed
