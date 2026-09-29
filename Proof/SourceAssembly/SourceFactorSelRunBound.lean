import Proof.MachineModel.Runs

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.RunBound
open NearCubicWires LocalBitMultitape ExtDecompositionBatch

/-- Writing one cell extends a tape to at most the written position. -/
theorem write_length_le (l : List Bool) (h : Nat) (v : Bool) :
    (writeTapeBit l h v).length ≤ max l.length (h + 1) := by
  induction l generalizing h with
  | nil =>
    induction h with
    | zero => simp [writeTapeBit]
    | succ h ih =>
      simp only [writeTapeBit, List.length_cons, List.length_nil] at ih ⊢
      omega
  | cons x t ih =>
    cases h with
    | zero => simp [writeTapeBit]
    | succ h =>
      simp only [writeTapeBit, List.length_cons]
      have := ih h
      omega

/-- One transition: heads move by at most one, tapes grow at most to the scanned cell. -/
theorem step_bound {t s : Nat} (p : Machine t s) (c d : Configuration t s)
    (hs : step p c = some d) (i : Fin t) :
    d.heads i ≤ c.heads i + 1 ∧ (d.tapes i).length ≤ max (c.tapes i).length (c.heads i + 1) := by
  unfold step at hs
  obtain ⟨action, _, he⟩ := Option.map_eq_some_iff.mp hs
  subst d
  refine ⟨?_, ?_⟩
  · simp only [applyAction]
    cases action.move i <;> simp only [HeadMove.apply] <;> omega
  · simp only [applyAction]
    cases action.write i with
    | none => exact le_max_left _ _
    | some v => exact write_length_le _ _ _

/-- A whole run of fuel `f`. -/
theorem runFrom_bound {t s : Nat} (p : Machine t s) (fuel : Nat) (c : Configuration t s)
    (r : ExecutionReceipt t s) (hr : runFrom p fuel c = some r) (i : Fin t) :
    r.final.heads i ≤ c.heads i + fuel ∧
      (r.final.tapes i).length ≤ max (c.tapes i).length (c.heads i + fuel + 1) := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact ⟨Nat.le_add_right _ _, le_max_left _ _⟩
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr
      exact ⟨Nat.le_add_right _ _, le_max_left _ _⟩
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases he : runFrom p fuel d with
        | none => simp [hs, he] at hr
        | some tail =>
          simp only [hs, he, Option.some.injEq] at hr
          subst r
          show tail.final.heads i ≤ c.heads i + (fuel + 1) ∧
            (tail.final.tapes i).length ≤ max (c.tapes i).length (c.heads i + (fuel + 1) + 1)
          obtain ⟨h1, l1⟩ := step_bound p c d hs i
          obtain ⟨h2, l2⟩ := ih d tail he
          refine ⟨by omega, ?_⟩
          refine l2.trans ?_
          apply max_le
          · exact l1.trans (max_le (le_max_left _ _) (le_max_of_le_right (by omega)))
          · exact le_max_of_le_right (by omega)

/-- **The `Step` form.** -/
theorem step_len {t s : Nat} {p : Machine t s} {n : Nat} {H : Fin t → Nat} {A : Fin t → List Bool}
    {H' : Fin t → Nat} {A' : Fin t → List Bool} (h : Step p n H A H' A') (i : Fin t) :
    H' i ≤ H i + n ∧ (A' i).length ≤ max (A i).length (H i + n + 1) := by
  obtain ⟨r, hr, hh, ht, _⟩ := h
  have b := runFrom_bound p n ⟨p.start, H, A⟩ r hr i
  rw [hh, ht] at b
  exact b

/-- **The window form** used for `ResidentRunH`'s length conjunct: a tape of length `≤ R` scanned from head `0` stays
within `R` under a run of cost `c` with `c + 1 ≤ R`. -/
theorem step_len_window {t s : Nat} {p : Machine t s} {n : Nat} {H : Fin t → Nat} {A : Fin t → List Bool}
    {H' : Fin t → Nat} {A' : Fin t → List Bool} (h : Step p n H A H' A') (R : Nat) (i : Fin t)
    (hA : (A i).length ≤ R) (hH : H i = 0) (hn : n + 1 ≤ R) : (A' i).length ≤ R := by
  have b := (step_len h i).2
  rw [hH] at b
  exact b.trans (max_le hA (by omega))

end NearCubicWires.SourceFactorSel.RunBound

