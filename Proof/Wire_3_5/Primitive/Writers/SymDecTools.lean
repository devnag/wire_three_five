import Proof.Wire_3_5.Primitive.Writers.SymDecIdx

/-! # PA (d)-SYM decode, part 7: tools (capacity invariant, block clearing, running sums over the counts)

* **`wexec_le`**: a register program keeps every register within the capacity (the only increment checks it);
* `zeroOut`, `clrsW`, **`clrs_spec`**: clearing a list of registers (values unknown, within the capacity);
* `sumItemsW`, **`sumItems_spec`**: `K` items of the counts stream `unaryList cs`, their sum added to a register.

Paper quantities of the main type: the SYM pool's slice lengths (their running sums: a slice's offset, the pool's
size). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

section Tools
variable {ns nr : ℕ} (cap : ℕ)

/-- **Every register stays within the capacity.** -/
theorem wexec_le {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    (∀ r, σ.val r ≤ cap) → ∀ r, τ.val r ≤ cap := by
  induction h with
  | skip => exact id
  | inc r σ hr =>
    intro hb q
    by_cases hq : q = r
    · subst hq; simp; omega
    · simp [Function.update_of_ne hq]; exact hb q
  | dec r σ hr =>
    intro hb q
    by_cases hq : q = r
    · subst hq; simp; have := hb q; omega
    · simp [Function.update_of_ne hq]; exact hb q
  | fwd i σ => intro hb q; simpa using hb q
  | bwd i σ => intro hb q; simpa using hb q
  | wr i b σ => intro hb q; simpa using hb q
  | setc v σ => intro hb q; simpa using hb q
  | seq _ _ ih1 ih2 => exact fun hb => ih2 (ih1 hb)
  | ifrT _ _ ih => exact ih
  | ifrF _ _ ih => exact ih
  | ifsT _ _ ih => exact ih
  | ifsF _ _ ih => exact ih
  | whrF _ => exact id
  | whrT _ _ _ ih1 ih2 => exact fun hb => ih2 (ih1 hb)
  | whsF _ => exact id
  | whsT _ _ _ ih1 ih2 => exact fun hb => ih2 (ih1 hb)
  | mono _ _ ih => exact ih

/-- The state with the listed registers zeroed. -/
def zeroOut (σ : WState ns nr) : List (Fin nr) → WState ns nr
  | [] => σ
  | r :: rs => zeroOut (σ.setv r 0) rs

/-- Clear the listed registers. -/
def clrsW : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clrsW rs)

theorem zeroOut_val : ∀ (rs : List (Fin nr)) (σ : WState ns nr) (q : Fin nr),
    (zeroOut σ rs).val q = if q ∈ rs then 0 else σ.val q
  | [], σ, q => by simp [zeroOut]
  | r :: rs, σ, q => by
    rw [zeroOut, zeroOut_val rs (σ.setv r 0) q]
    by_cases hq : q = r
    · subst hq; simp
    · by_cases hm : q ∈ rs
      · simp [hm]
      · simp [hm, hq, Function.update_of_ne hq]

theorem zeroOut_st : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (zeroOut σ rs).st = σ.st
  | [], σ => rfl
  | r :: rs, σ => by rw [zeroOut, zeroOut_st rs]; rfl

theorem zeroOut_sh : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (zeroOut σ rs).sh = σ.sh
  | [], σ => rfl
  | r :: rs, σ => by rw [zeroOut, zeroOut_sh rs]; rfl

theorem zeroOut_cell : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (zeroOut σ rs).cell = σ.cell
  | [], σ => rfl
  | r :: rs, σ => by rw [zeroOut, zeroOut_cell rs]; rfl

/-- **Clearing registers** of unknown values within the capacity. -/
theorem clrs_spec : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (∀ r, σ.val r ≤ cap) →
    WExec cap (clrsW rs) σ (zeroOut σ rs) (rs.length * (3 * cap + 2))
  | [], σ, _ => WExec.mono (WExec.skip σ) (by simp)
  | r :: rs, σ, hb => by
    have h1 := wclear_spec cap r (σ.val r) σ rfl (hb r)
    have h2 := clrs_spec rs (σ.setv r 0) (fun q => by
      by_cases hq : q = r
      · subst hq; simp
      · simp [Function.update_of_ne hq]; exact hb q)
    refine WExec.mono (WExec.seq h1 h2) ?_
    have := hb r
    simp only [List.length_cons]
    nlinarith

end Tools

section Sums

end Sums

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
