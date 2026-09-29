import Proof.Wire_3_5.FinalPass.SdSet6

/-! # S4 (the seeds phase), part 34: the seed loop and the teardown (P3:3044-3048, 3170-3178)

**`loopTd E = seedLoop E ; tdW`**; **`loopTd_spec`**: from the loops' entry state `ωQ` (the seed loop's hypotheses
`QHyp`, its invariant at accumulator `0`, the tables word `twW FP es L₀ L₁`, every register `0` but the setup's
and the evaluator's numbers), the numerator stream holds `frame (binary W (Σ_{e ∈ es} Gs e))`, every register is `0`,
the heads, the cell and every kept stream but the two tables as at `ωQ`.

Paper quantity of the main type: the printed numerator `Σ_e Σ_c Σ_ℓ M(e,x)·Σ R̂(x)` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

theorem lsum_le {α : Type} : ∀ (l : List α) (f : α → ℕ) (c : ℕ), (∀ x ∈ l, f x ≤ c) → (l.map f).sum ≤ l.length * c
  | [], _, _, _ => by simp
  | x :: l, f, c, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := lsum_le l f c (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 := h x List.mem_cons_self
    rw [Nat.succ_mul]
    omega

/-- The teardown's step bound. -/
def tdCost (cap nn : ℕ) : ℕ := 12 * (3 * cap + 2) + 4 * (3 * cap + 2) + nn * (3 * cap + 2) + 2

variable (E : SymPtEval2)

/-- The seed loop, then the teardown. -/
noncomputable def loopTd : BP E.nw E.nn E.nsc E.nrs := .seq (seedLoop E) tdW

theorem loopTd_spec (cap : ℕ) (FP : GapParams) (P : StarParams) (σT : P.Translation)
    (carriers : List (Stars.Carrier P.n)) {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n)
    (Vf : BitInput P.n → Fin N → Fin N → ℕ) (s bb h tl W T nE Vm Bd : ℕ) (ωQ : BS E.nw E.nn E.nsc E.nrs)
    (H : QHyp E cap FP P σT carriers ps eu ev Vf s bb h tl T nE Vm ωQ) (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T)
    (es : List (GapSeed FP)) (hI : SdInv FP P carriers W 0 ωQ ωQ) (hP : ωQ.val rgP = 0) (hF : ωQ.val fS = 0)
    (hTW : ωQ.st tTW = twW FP es (Seams.carLen carriers 0) (Seams.carLen carriers 1))
    (hb : (es.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum ≤ Bd)
    (hz : ∀ q, q ∉ (tdFix : List (Fin (bnr E.nn E.nrs))) → q ∉ (thrRegs : List (Fin (bnr E.nn E.nrs))) →
      q ∉ (symRegs : List (Fin (bnr E.nn E.nrs))) → ωQ.val q = 0)
    (hc : ∀ q, ωQ.val q ≤ cap) :
    ∃ ω : BS E.nw E.nn E.nsc E.nrs, ∃ m, WExec cap (loopTd E) ωQ ω m ∧
      m ≤ slCost FP P carriers ps.length s bb h tl nE Vm T (ωQ.st tTW).length es + 9 + 1 + tdCost cap E.nn ∧
      ω.st tN = frame (binary W (es.map fun e => Gs FP e P σT carriers ps eu ev Vf).sum) ∧
      ω.sh = ωQ.sh ∧ (∀ q, ω.val q = 0) ∧ ω.cell = ωQ.cell ∧
      (∀ i, KeptC i → i ≠ tT 0 → i ≠ tT 1 → ω.st i = ωQ.st i) := by
  obtain ⟨ω1, e1, hI1, hF1, hP1⟩ := seedLoop_spec E cap FP P σT carriers ps eu ev Vf s bb h tl W T nE Vm Bd ωQ H
    hBW hBT es 0 ωQ hI hP hF hTW (by rw [Nat.zero_add]; exact hb)
  rw [Nat.zero_add] at hI1
  have v1 : ∀ q, q ≠ rgP → q ≠ fS → ω1.val q = ωQ.val q := hI1.val
  have c1 : ∀ q, ω1.val q ≤ cap := fun q => by
    by_cases hq1 : q = rgP
    · rw [hq1]
      have := H.twc
      rw [hTW] at this
      omega
    · by_cases hq2 : q = fS
      · rw [hq2, hF1]; omega
      · rw [v1 q hq1 hq2]; exact hc q
  obtain ⟨m2, e2, hm2⟩ := tdW_spec cap ω1 c1
  have b1 := lsum_le (tdFix : List (Fin (bnr E.nn E.nrs))) (fun r => 3 * ω1.val r + 2) (3 * cap + 2)
    (fun r _ => by have := c1 r; omega)
  have b2 := lsum_le (thrRegs : List (Fin (bnr E.nn E.nrs))) (fun r => 3 * ω1.val r + 2) (3 * cap + 2)
    (fun r _ => by have := c1 r; omega)
  have b3 := lsum_le (symRegs : List (Fin (bnr E.nn E.nrs))) (fun r => 3 * ω1.val r + 2) (3 * cap + 2)
    (fun r _ => by have := c1 r; omega)
  have l1 : (tdFix : List (Fin (bnr E.nn E.nrs))).length = 12 := rfl
  have l2 : (thrRegs : List (Fin (bnr E.nn E.nrs))).length = 4 := rfl
  have l3 : (symRegs : List (Fin (bnr E.nn E.nrs))).length = E.nn := by simp [symRegs]
  rw [l1] at b1
  rw [l2] at b2
  rw [l3] at b3
  refine ⟨_, _, WExec.seq e1 e2, by unfold tdCost; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [clApply_st, clApply_st, clApply_st]; exact hI1.Nw
  · rw [clApply_sh, clApply_sh, clApply_sh]; exact hI1.sh
  · intro q
    rw [clApply_val]
    dsimp only
    split_ifs with h3
    · rfl
    · rw [clApply_val]
      dsimp only
      split_ifs with h2
      · rfl
      · rw [clApply_val]
        dsimp only
        split_ifs with h1
        · rfl
        · have hq1 : q ≠ rgP := fun e => h1 (by rw [e]; simp [tdFix])
          by_cases hq2 : q = fS
          · rw [hq2, hF1]
          · rw [v1 q hq1 hq2]; exact hz q h1 h2 h3
  · rw [clApply_cell, clApply_cell, clApply_cell]; exact hI1.cell
  · intro i hi h0 h1
    rw [clApply_st, clApply_st, clApply_st]; exact hI1.st i hi h0 h1

end NearCubicWires.WireExponent3_5.FinalPass.Sd
