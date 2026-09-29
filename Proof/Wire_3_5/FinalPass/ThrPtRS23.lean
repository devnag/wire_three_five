import Proof.Wire_3_5.FinalPass.ThrPtRS22
import Proof.Wire_3_5.FinalPass.SeamsPt2

/-! # S2 (THR per point), part 37: the internal layout inside any per-point layout (P3:3170-3178)

`sOf`, `rOf`: the internal streams (`0 … 2` the point, `3 … 9` the call's words, `10 … 16` the scratch) and
registers (`0` the accumulator; `5, 109, 8, 63` the call's numbers `a, |𝒢|, τ₀, |occs|`; the other 113 the scratch
registers) as indices of the per-point layout `S`, `R` (both injective, by their left inverses). `view0 σ`: the
internal entry read off `σ`, the scratch emptied. **`transport`**: an internal run from `view0 σ` that ends with the
accumulator `v`, every other register, head and the cell as at entry, the call's streams unchanged and the scratch
blank, lifted (`wexec_pad`, then `WExec.liftW`) is a run of the lifted program meeting `PtOut S R σ τ v`.
Paper quantity: none beyond the machine model (the per-point seam). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The internal streams as per-point stream indices. -/
def sOf (j : Fin 17) : Fin 3 ⊕ Fin 7 ⊕ Fin 7 :=
  if h : j.val < 3 then .inl ⟨j.val, h⟩ else if h' : j.val < 10 then .inr (.inl ⟨j.val - 3, by omega⟩)
  else .inr (.inr ⟨j.val - 10, by omega⟩)

def sInv : Fin 3 ⊕ Fin 7 ⊕ Fin 7 → Fin 17
  | .inl i => ⟨i.val, by omega⟩
  | .inr (.inl i) => ⟨i.val + 3, by omega⟩
  | .inr (.inr i) => ⟨i.val + 10, by omega⟩

theorem sInv_sOf : ∀ j : Fin 17, sInv (sOf j) = j := by decide

theorem sOf_inj : Function.Injective sOf := Function.LeftInverse.injective sInv_sOf

theorem sOf_scr : ∀ j : Fin 7, sOf ⟨j.val + 10, by omega⟩ = .inr (.inr j) := by decide

/-- The scratch registers' indices. -/
def sIdx (q : ℕ) : ℕ :=
  q - 1 - (if 5 < q then 1 else 0) - (if 8 < q then 1 else 0) - (if 63 < q then 1 else 0) - (if 109 < q then 1 else 0)

theorem sIdx_lt (q : Fin 118) : sIdx q.val < 113 := by
  have := q.isLt
  unfold sIdx
  split_ifs <;> omega

/-- The internal registers as per-point register indices. -/
def rOf (q : Fin 118) : Fin 1 ⊕ Fin 4 ⊕ Fin 113 :=
  if q.val = 0 then .inl 0 else if q.val = 5 then .inr (.inl 0) else if q.val = 109 then .inr (.inl 1)
  else if q.val = 8 then .inr (.inl 2) else if q.val = 63 then .inr (.inl 3) else .inr (.inr ⟨sIdx q.val, sIdx_lt q⟩)

def unIdx (j : ℕ) : ℕ :=
  if j < 4 then j + 1 else if j < 6 then j + 2 else if j < 60 then j + 3 else if j < 105 then j + 4 else j + 5

def rInv : Fin 1 ⊕ Fin 4 ⊕ Fin 113 → Fin 118
  | .inl _ => 0
  | .inr (.inl i) => ![5, 109, 8, 63] i
  | .inr (.inr j) => ⟨unIdx j.val, by have := j.isLt; unfold unIdx; split_ifs <;> omega⟩

theorem rInv_rOf : ∀ q : Fin 118, rInv (rOf q) = q := by decide

theorem rOf_inj : Function.Injective rOf := Function.LeftInverse.injective rInv_rOf

section Transport
variable {ns nr : ℕ} (S : Fin 3 ⊕ Fin 7 ⊕ Fin 7 ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin 4 ⊕ Fin 113 ↪ Fin nr)

def fS : Fin 17 → Fin (ns + 1) := fun j => S (sOf j)

def fR : Fin 118 → Fin nr := fun q => R (rOf q)

theorem fS_inj : Function.Injective (fS S) := fun _ _ h => sOf_inj (S.injective h)

theorem fR_inj : Function.Injective (fR R) := fun _ _ h => rOf_inj (R.injective h)

/-- The internal view of `σ`. -/
def view (σ : WState ns nr) : WState 16 118 :=
  ⟨fun j => σ.sh (fS S j), fun j => σ.st (fS S j), fun q => σ.val (fR R q), σ.cell⟩

/-- The internal view of `σ`, the scratch emptied. -/
def view0 (σ : WState ns nr) : WState 16 118 :=
  ⟨fun j => σ.sh (fS S j), fun j => if 10 ≤ j.val then [] else σ.st (fS S j), fun q => σ.val (fR R q), σ.cell⟩

/-- The scratch's lengths. -/
def blankK (σ : WState ns nr) : Fin 17 → ℕ := fun j => if 10 ≤ j.val then (σ.st (fS S j)).length else 0

theorem lift_view (σ : WState ns nr) : LiftW (fS S) (fR R) σ (view S R σ) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem fS_scr (j : Fin 17) (h : 10 ≤ j.val) : fS S j = S (.inr (.inr ⟨j.val - 10, by omega⟩)) := by
  have e := sOf_scr ⟨j.val - 10, by omega⟩
  have hj : (⟨j.val - 10 + 10, by omega⟩ : Fin 17) = j := Fin.ext (by simp; omega)
  rw [hj] at e
  simp only [fS, e]

theorem view_pad (σ : WState ns nr) (hsc : ∀ j, ∀ b ∈ σ.st (S (.inr (.inr j))), b = false) :
    padAll (view0 S R σ) (blankK S σ) = view S R σ := by
  apply WState.eq
  · rfl
  · funext j
    by_cases h : 10 ≤ j.val
    · simp only [padAll, view0, blankK, view, if_pos h, pad_nil]
      rw [fS_scr S j h]
      exact (eq_rep_false _ (hsc _)).symm
    · simp only [padAll, view0, blankK, view, if_neg h, pad_zero]
  · rfl
  · rfl

theorem mem_pad (l : List Bool) (k : ℕ) (b : Bool) (h : b ∈ pad l k) : b ∈ l ∨ b = false := by
  unfold pad at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_replicate.mp h).2

variable (cap : ℕ)

/-- **An internal run, lifted, meets the per-point exit.** -/
theorem transport (P : TProg) (σ : WState ns nr) (hsc : ∀ j, ∀ b ∈ σ.st (S (.inr (.inr j))), b = false)
    (v n : ℕ) (τf : WState 16 118) (e : WExec cap P (view0 S R σ) τf n)
    (hv : τf.val = Function.update (view0 S R σ).val 0 v) (hsh : τf.sh = (view0 S R σ).sh)
    (hcell : τf.cell = (view0 S R σ).cell) (hst : ∀ i : Fin 17, i.val < 10 → τf.st i = (view0 S R σ).st i)
    (hsc' : ∀ i : Fin 17, 10 ≤ i.val → ∀ b ∈ τf.st i, b = false) :
    ∃ τ, WExec cap (P.liftW (fS S) (fR R)) σ τ n ∧ Seams.PtOut S R σ τ v := by
  have e2 := wexec_pad e (blankK S σ)
  rw [view_pad S R σ hsc] at e2
  obtain ⟨ω', e3, hL, hO⟩ := WExec.liftW cap cap le_rfl (fS S) (fS_inj S) (fR R) (fR_inj R) e2 σ (lift_view S R σ)
  have h0 : fR R 0 = R (.inl 0) := rfl
  refine ⟨ω', e3, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · funext q
    by_cases hq : ∃ r, fR R r = q
    · obtain ⟨r, rfl⟩ := hq
      rw [hL.val r, padAll_val, hv]
      by_cases hr : r = 0
      · subst hr
        rw [h0, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hr, Function.update_of_ne (fun h => hr (fR_inj R (h.trans h0.symm)))]
        rfl
    · push Not at hq
      rw [hO.2 q hq, Function.update_of_ne (fun h => hq 0 (h0.trans h.symm))]
  · funext j
    by_cases hj : ∃ i, fS S i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hL.sh i, padAll_sh, hsh]
      rfl
    · push Not at hj
      exact (hO.1 j hj).1
  · rw [hL.cell, padAll_cell, hcell]
    rfl
  · intro i hi
    by_cases hj : ∃ k, fS S k = i
    · obtain ⟨k, rfl⟩ := hj
      have hk : k.val < 10 := by
        by_contra hk
        exact hi ⟨k.val - 10, by omega⟩ (fS_scr S k (by omega))
      rw [hL.st k, padAll_st, hst k hk]
      simp only [view0, blankK, if_neg (show ¬ 10 ≤ k.val by omega), pad_zero]
    · push Not at hj
      exact (hO.1 i hj).2
  · intro jj b hb
    have hk : S (.inr (.inr jj)) = fS S ⟨jj.val + 10, by omega⟩ := by
      rw [fS_scr S _ (by simp)]
      congr
    rw [hk, hL.st, padAll_st] at hb
    rcases mem_pad _ _ b hb with h | h
    · exact hsc' _ (by simp) b h
    · exact h

end Transport

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
