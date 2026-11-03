import Proof.SourceAssembly.SourceFactorSelWordsLocal

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
noncomputable section

/-- Host values of the shared ports `6..28` and of W's region. -/
def hostV (P0 w tc B Pc wB : Nat) (p : Nat) : Nat :=
  if p < 11 then B + 43 + Pc + (p - 6)
  else if p < 15 then P0 + 378 + (p - 11)
  else if p < 20 then P0 + 393 + w + tc + (p - 15)
  else if p < 22 then P0 + 402 + w + tc + (p - 20)
  else if p < 24 then P0 + 405 + w + tc + (p - 22)
  else if p < 25 then B
  else if p < 26 then P0 + 98
  else if p < 29 then P0 + 224 + (p - 26)
  else wB + (p - 29)

section dec

end dec

/-- The value classes of `hostV` (one characterization, used for the range facts). -/
theorem hostV_cases (P0 w tc B Pc wB p : Nat) (h6 : 6 ≤ p) :
    (p < 11 ∧ hostV P0 w tc B Pc wB p = B + 43 + Pc + (p - 6)) ∨
    (11 ≤ p ∧ p < 29 ∧ (hostV P0 w tc B Pc wB p = P0 + 378 + (p - 11) ∧ p < 15 ∨
      hostV P0 w tc B Pc wB p = P0 + 393 + w + tc + (p - 15) ∧ 15 ≤ p ∧ p < 20 ∨
      hostV P0 w tc B Pc wB p = P0 + 402 + w + tc + (p - 20) ∧ 20 ≤ p ∧ p < 22 ∨
      hostV P0 w tc B Pc wB p = P0 + 405 + w + tc + (p - 22) ∧ 22 ≤ p ∧ p < 24 ∨
      hostV P0 w tc B Pc wB p = B ∧ p = 24 ∨
      hostV P0 w tc B Pc wB p = P0 + 98 ∧ p = 25 ∨
      hostV P0 w tc B Pc wB p = P0 + 224 + (p - 26) ∧ 26 ≤ p)) ∨
    (29 ≤ p ∧ hostV P0 w tc B Pc wB p = wB + (p - 29)) := by
  unfold hostV
  by_cases c1 : p < 11
  · left; exact ⟨c1, by rw [if_pos c1]⟩
  rw [if_neg c1]
  by_cases c8 : p < 29
  · right; left
    refine ⟨by omega, c8, ?_⟩
    by_cases c2 : p < 15
    · left; exact ⟨by rw [if_pos c2], c2⟩
    rw [if_neg c2]
    by_cases c3 : p < 20
    · right; left; exact ⟨by rw [if_pos c3], by omega, c3⟩
    rw [if_neg c3]
    by_cases c4 : p < 22
    · right; right; left; exact ⟨by rw [if_pos c4], by omega, c4⟩
    rw [if_neg c4]
    by_cases c5 : p < 24
    · right; right; right; left; exact ⟨by rw [if_pos c5], by omega, c5⟩
    rw [if_neg c5]
    by_cases c6 : p < 25
    · right; right; right; right; left; exact ⟨by rw [if_pos c6], by omega⟩
    rw [if_neg c6]
    by_cases c7 : p < 26
    · right; right; right; right; right; left; exact ⟨by rw [if_pos c7], by omega⟩
    rw [if_neg c7, if_pos c8]
    right; right; right; right; right; right; exact ⟨rfl, by omega⟩
  · right; right
    refine ⟨by omega, ?_⟩
    have hc : ¬ p < 15 ∧ ¬ p < 20 ∧ ¬ p < 22 ∧ ¬ p < 24 ∧ ¬ p < 25 ∧ ¬ p < 26 := by omega
    rw [if_neg hc.1, if_neg hc.2.1, if_neg hc.2.2.1, if_neg hc.2.2.2.1, if_neg hc.2.2.2.2.1, if_neg hc.2.2.2.2.2,
      if_neg c8]

/-- **The dock.** -/
def wsl {V N : Nat} (src : Fin 6 → Fin V) (P0 w tc B Pc wB : Nat)
    (hV : ∀ p, 6 ≤ p → p < N → hostV P0 w tc B Pc wB p < V) : Fin N → Fin V :=
  fun p => if h : p.val < 6 then src ⟨p.val, h⟩ else ⟨hostV P0 w tc B Pc wB p.val, hV p.val (by omega) p.isLt⟩

section dock

end dock

end
end NearCubicWires.SourceFactorSel.WordsHost

