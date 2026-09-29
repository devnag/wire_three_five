import Proof.Wire_3_5.Primitive.Writers.WriteNat

/-! # SB, part 18: registers stay within the capacity; clearing a register list

* **`WExec.val_le`**: a word program's run keeps every register `≤ cap` (only `inc`, guarded by `< cap`, raises one);
* `clearAllW`, `clearAllCost`, **`clearAll_spec`**: every listed register to `0` (each within the capacity), every
  stream, head, the cell and every other register unchanged.

Paper quantity: none (plumbing: a writer ends with every register `0`, `CoreWordsMJ`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBInv
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ} (cap : ℕ)

theorem WExec.val_le {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    (∀ r, σ.val r ≤ cap) → ∀ r, τ.val r ≤ cap := by
  induction h with
  | skip σ => exact id
  | inc r σ hv =>
    intro hσ q
    by_cases hq : q = r
    · subst hq; simp; omega
    · simp [Function.update_of_ne hq]; exact hσ q
  | dec r σ hv =>
    intro hσ q
    by_cases hq : q = r
    · subst hq; simp; have := hσ q; omega
    · simp [Function.update_of_ne hq]; exact hσ q
  | fwd i σ => exact id
  | bwd i σ => exact id
  | wr i b σ => exact id
  | setc v σ => exact id
  | seq _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | ifrT _ _ ih => exact ih
  | ifrF _ _ ih => exact ih
  | ifsT _ _ ih => exact ih
  | ifsF _ _ ih => exact ih
  | whrF _ => exact id
  | whrT _ _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | whsF _ => exact id
  | whsT _ _ _ ih1 ih2 => exact fun hσ => ih2 (ih1 hσ)
  | mono _ _ ih => exact ih

/-- Clear every listed register. -/
def clearAllW : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: l => .seq (WM.clear r) (clearAllW l)

def clearAllCost : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * cap + 1 + 1 + clearAllCost k

theorem clearAll_spec : ∀ (l : List (Fin nr)) (σ : WState ns nr), (∀ r, σ.val r ≤ cap) →
    ∃ τ : WState ns nr, WExec cap (clearAllW l) σ τ (clearAllCost cap l.length) ∧ (∀ r ∈ l, τ.val r = 0) ∧
      (∀ r, r ∉ l → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro σ _
    exact ⟨σ, WExec.skip σ, fun r hr => by simp at hr, fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons r l ih =>
    intro σ hσ
    have e1 := wclear_spec cap r (σ.val r) σ rfl (hσ r)
    have hσ1 : ∀ q, (σ.setv r 0).val q ≤ cap := by
      intro q; by_cases hq : q = r
      · subst hq; simp
      · simp [Function.update_of_ne hq]; exact hσ q
    obtain ⟨τ, e2, hin, hout, hst, hsh, hcl⟩ := ih (σ.setv r 0) hσ1
    refine ⟨τ, WExec.mono (WExec.seq e1 e2) (by simp [clearAllCost]; have := hσ r; omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with e | e
      · subst e
        by_cases hql : q ∈ l
        · exact hin q hql
        · rw [hout q hql]; simp
      · exact hin q e
    · intro q hq
      have hq1 : q ≠ r := fun e => hq (e ▸ List.mem_cons_self)
      have hq2 : q ∉ l := fun e => hq (List.mem_cons_of_mem _ e)
      rw [hout q hq2]; simp [Function.update_of_ne hq1]
    · rw [hst]; rfl
    · rw [hsh]; rfl
    · rw [hcl]; rfl

end NearCubicWires.WireExponent3_5.PrimAsm.SBInv
