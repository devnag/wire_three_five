import Proof.CaseAnalysis.FinalTailFeedPrep
import Proof.Hierarchy.CompetitorRecordRewind

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

/-- **Stage — widen one framed word.** Tape `2` of the block receives the widened
word, tape `0` keeps the driver; heads are untouched. -/
theorem norm_stage (slots : Fin 5 → Fin bank) (hi : Function.Injective slots)
    (width : ℕ) (bits : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (slots j) = 0)
    (hA : ∀ j, A (slots j) = ClockNormalize.input width bits j) :
    ∃ (s : ℕ) (m : Machine bank s) (A' : Fin bank → List Bool),
      Step m (4*width+4) H A H A' ∧
      A' (slots 2) = frame (ClockNormalize.resize width bits) ∧
      A' (slots 0) = List.replicate width true ∧
      (∀ i, (∀ j, slots j ≠ i) → A' i = A i) := by
  refine ⟨_, _, _, normalize_dock_at slots hi width bits H A hH hA, ?_, ?_, ?_⟩
  · exact install_slot slots hi A (normalizeOut width bits) 2
  · exact install_slot slots hi A (normalizeOut width bits) 0
  · intro i hin
    exact install_other slots A (normalizeOut width bits) i hin

/-- **Stage — lift field `k` of a record onto a blank tape.** The record survives;
both heads advance past the copy. -/
theorem field_stage (b : ℕ) (est : CompetitorValidity.Estimate) (count den : ℕ) (k : Fin 6)
    (src dst : Fin bank) (hne : src ≠ dst)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsrcH : H src = fieldCursor b est count den k) (hdstH : H dst = 0)
    (hsrcA : A src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den)
    (hdstA : A dst = []) :
    ∃ (s : ℕ) (m : Machine bank s) (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step m (2*(field b est count den k).length+1) H A H' A' ∧
      A' dst = frame (field b est count den k) ∧
      A' src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den ∧
      H' src = fieldCursor b est count den k + 2*(field b est count den k).length+1 ∧
      H' dst = 2*(field b est count den k).length+1 ∧
      (∀ i, src ≠ i → dst ≠ i → A' i = A i) ∧
      (∀ i, src ≠ i → dst ≠ i → H' i = H i) := by
  have hstep := field_dock b est count den k src dst hne H A hsrcH (by simp [hdstH, hdstA]) hsrcA
  refine ⟨_, _, _, _, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : install (pairSlots src dst) A
        ![CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den,
          A dst ++ frame (field b est count den k)] dst
        = A dst ++ frame (field b est count den k) := pairA1 src dst hne A _
    rw [h]
    simp [hdstA]
  · exact pairA0 src dst hne A _
  · exact pairH0 src dst hne H _
  · have h : dockH (pairSlots src dst) H
        ![fieldCursor b est count den k + 2*(field b est count den k).length+1,
          (A dst ++ frame (field b est count den k)).length] dst
        = (A dst ++ frame (field b est count den k)).length := pairH1 src dst hne H _
    rw [h]
    simp [hdstA]
  · intro i hs hd
    exact pairAout src dst A _ i hs hd
  · intro i hs hd
    exact pairHout src dst H _ i hs hd

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

/-- **Stage — one paid head reset**, docked at `src` with driver `drv` and log
`log`. The word and the driver survive; both their heads return to `0`. -/
theorem rewind_stage (src drv log : Fin bank) (hsd : src ≠ drv) (hsl : src ≠ log)
    (hdl : drv ≠ log) (C pos : ℕ) (hpos : pos ≤ C) (source : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsH : H src = pos) (hdH : H drv = 0) (hlH : H log = 0)
    (hsA : A src = source) (hdA : A drv = List.replicate C true) (hlA : A log = []) :
    ∃ (s : ℕ) (m : Machine bank s) (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step m (2*C+2) H A H' A' ∧
      A' src = source ∧ A' drv = List.replicate C true ∧
      H' src = 0 ∧ H' drv = 0 ∧
      (∀ i, src ≠ i → drv ≠ i → log ≠ i → A' i = A i) ∧
      (∀ i, src ≠ i → drv ≠ i → log ≠ i → H' i = H i) := by
  have hinj := triSlots_injective src drv log hsd hsl hdl
  have hstep := (rewind_base source C pos hpos).dock (triSlots src drv log) hinj H A
    (by
      intro j
      fin_cases j
      · exact hsH
      · exact hdH
      · exact hlH)
    (by
      intro j
      fin_cases j
      · exact hsA
      · exact hdA
      · exact hlA)
  refine ⟨_, _, _, _, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact triA0 src drv log hsd hsl hdl A _
  · exact triA1 src drv log hsd hsl hdl A _
  · exact triH0 src drv log hsd hsl hdl H _
  · exact triH1 src drv log hsd hsl hdl H _
  · intro i h1 h2 h3
    exact triAout src drv log A _ i h1 h2 h3
  · intro i h1 h2 h3
    exact triHout src drv log H _ i h1 h2 h3

/-! ### The three record fields the comparator needs, and their cursors -/

theorem field_pos (W : ℕ) (est : CompetitorValidity.Estimate) :
    field (w W) est 1 1 0 = binary (w2 W) est.positive := rfl
theorem field_neg (W : ℕ) (est : CompetitorValidity.Estimate) :
    field (w W) est 1 1 1 = binary (w2 W) est.negative := rfl
theorem field_den (W : ℕ) (est : CompetitorValidity.Estimate) :
    field (w W) est 1 1 2 = binary (w2 W) est.denominator := rfl

theorem field_pos_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field (w W) est 1 1 0).length = w2 W := by
  rw [field_pos, binary_length]
theorem field_neg_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field (w W) est 1 1 1).length = w2 W := by
  rw [field_neg, binary_length]
theorem field_den_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field (w W) est 1 1 2).length = w2 W := by
  rw [field_den, binary_length]

theorem cursor_pos (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor (w W) est 1 1 0 = 0 := fieldCursor_zero (w W) est 1 1

theorem cursor_neg (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor (w W) est 1 1 1 = 2*(w2 W)+1 := by
  have h : fieldCursor (w W) est 1 1 1
      = fieldCursor (w W) est 1 1 0 + 2*(field (w W) est 1 1 0).length + 1 :=
    fieldCursor_succ (w W) est 1 1 0 (by decide)
  rw [h, cursor_pos, field_pos_length, Nat.zero_add]

theorem cursor_den (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor (w W) est 1 1 2 = 4*(w2 W)+2 := by
  have h : fieldCursor (w W) est 1 1 2
      = fieldCursor (w W) est 1 1 1 + 2*(field (w W) est 1 1 1).length + 1 :=
    fieldCursor_succ (w W) est 1 1 1 (by decide)
  rw [h, cursor_neg, field_neg_length]
  omega

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
