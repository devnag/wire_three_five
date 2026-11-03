import Proof.Wire_3_5.FinalPass.S5TBld

/-! # S5-THR, part 16: register bounds, clearing, erasing (P3:3170-3181)

The THR half ends with every register at `0` (its register tapes blank) and the top power `sent W` erased; the
scrub (`BlockScrub`) blanks the rest.

* **`WExec.val_le`**: a word program keeps every register within the capacity;
* `clearL` / **`clearL_spec`**, `clearAll` / **`clearAll_spec`**: every register to `0`, whatever its value;
* `eraseS` / **`eraseS_spec`**: a sentinel word `sent W` overwritten by `W + 1` zeros, its head back at `0`;
* `appendO_wSt` (PA's `appendO` is the written state `wSt` at an end head).

Paper quantity: none (the machine's clean exit, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-- **Every register stays within the capacity.** -/
theorem WExec.val_le {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    (∀ r, σ.val r ≤ cap) → ∀ r, τ.val r ≤ cap := by
  induction h with
  | skip => exact fun h => h
  | inc r σ hv =>
    intro h q
    simp only [WState.setv_val, Function.update_apply]
    split_ifs with hq
    · omega
    · exact h q
  | dec r σ hv =>
    intro h q
    simp only [WState.setv_val, Function.update_apply]
    split_ifs with hq
    · subst hq; have := h q; omega
    · exact h q
  | fwd => exact fun h => h
  | bwd => exact fun h => h
  | wr => exact fun h => h
  | setc => exact fun h => h
  | seq _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | ifrT _ _ ih => exact ih
  | ifrF _ _ ih => exact ih
  | ifsT _ _ ih => exact ih
  | ifsF _ _ ih => exact ih
  | whrF _ => exact fun h => h
  | whrT _ _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | whsF _ => exact fun h => h
  | whsT _ _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | mono _ _ ih => exact ih

/-- Clear the listed registers. -/
def clearL : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clearL rs)

theorem clearL_spec : ∀ (rs : List (Fin nr)) (σ : WState ns nr), (∀ r, σ.val r ≤ cap) →
    ∃ τ, WExec cap (clearL rs) σ τ (rs.length * (3 * cap + 2)) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      (∀ r ∈ rs, τ.val r = 0) ∧ (∀ r, r ∉ rs → τ.val r = σ.val r)
  | [], σ, _ => ⟨σ, WExec.cast cap (WExec.skip σ) rfl (by simp), rfl, rfl, rfl, fun r h => by simp at h,
    fun _ _ => rfl⟩
  | r :: rs, σ, h => by
    have e1 := wclear_spec cap r (σ.val r) σ rfl (h r)
    obtain ⟨τ, e2, h1, h2, h3, h4, h5⟩ := clearL_spec rs (σ.setv r 0) (fun q => by
      simp only [WState.setv_val, Function.update_apply]
      split_ifs
      · omega
      · exact h q)
    refine ⟨τ, WExec.mono (WExec.seq e1 e2) ?_, h1, h2, h3, ?_, ?_⟩
    · have := h r
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · intro q hq
      by_cases hq' : q ∈ rs
      · exact h4 q hq'
      · rcases List.mem_cons.1 hq with e | e
        · subst e; rw [h5 q hq']; simp
        · exact absurd e hq'
    · intro q hq
      have hq1 : q ≠ r := fun e => hq (e ▸ List.mem_cons_self)
      rw [h5 q (fun h' => hq (List.mem_cons_of_mem _ h'))]
      simp [Function.update_apply, hq1]

/-- Clear every register. -/
def clearAll : WM ns nr := clearL (List.finRange nr)

theorem clearAll_spec (σ : WState ns nr) (h : ∀ r, σ.val r ≤ cap) :
    ∃ τ, WExec cap (clearAll (ns := ns) (nr := nr)) σ τ (nr * (3 * cap + 2)) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell ∧ ∀ r, τ.val r = 0 := by
  obtain ⟨τ, e, h1, h2, h3, h4, _⟩ := clearL_spec cap (List.finRange nr) σ h
  rw [List.length_finRange] at e
  exact ⟨τ, e, h1, h2, h3, fun r => h4 r (List.mem_finRange r)⟩

/-- The erase loop: overwrite ones by zeros. -/
def eraseLoop (X : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .whs X (.seq (.wr X false) (WM.fwdC X K))

/-- **Erase a sentinel word**: `sent W` becomes `W + 1` zeros, the head back at `0`. -/
def eraseS (X : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .seq (WM.fwdC X K) (.seq (eraseLoop X K) (WM.rewind X K))

/-- PA's `appendO` at an end head is the written state. -/
theorem appendO_wSt (σ : WState ns nr) (O : Fin (ns + 1)) (KW : Fin nr) (u : List Bool)
    (hO : σ.sh O = (σ.st O).length) : PrimAsm.WriteNat.appendO σ O KW u = wSt O KW σ u := by
  apply WState.eq
  · funext i; by_cases hi : i = O
    · subst hi; simp [PrimAsm.WriteNat.appendO, wSt, hO]
    · simp [PrimAsm.WriteNat.appendO, wSt, Function.update_apply, hi]
  · rfl
  · rfl
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
