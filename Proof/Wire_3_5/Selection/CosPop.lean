import Proof.Wire_3_5.Selection.CosIdx

/-! # C1.5: one population's row count and its weighted step (P3:1356-1362)

Paper: "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357); "Repeated
labelled occurrences are charged with their weights; they need not be deduplicated" (P3:1361-1362). One population
`X` of the population table: `TX := 0`; read its index count; for each index, `idxB` (`TX += rowsAt i`); read the
weight's numerator and denominator; then C6's `ratStepB`: `(AN, AD) := ratAccStep (AN, AD) (num, den, TX)`. Main
declarations: `idxL`, **`idxL_spec`**. Paper quantity: a population's exact row count at a candidate coset. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-- **The index loop**: `MC = Q 53` rounds of `idxB`. -/
def idxL (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) : WM ns nr :=
  .whr (Q 53) (.seq (.dec (Q 53)) (idxB S Q))

/-- The index words of a list. -/
def idxWords (W : ℕ) (l : List ℕ) : List Bool := (l.map fun i => frame (binary W i)).flatten

theorem idxWords_length (W : ℕ) (l : List ℕ) : (idxWords W l).length = l.length * (2 * W + 1) := by
  induction l with
  | nil => simp [idxWords]
  | cons a l ih =>
    simp only [idxWords, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih, RepairOrdinary.frame_length, binary_length]; ring

/-- **The index loop**: from `MC = |l|` with the table's head at `l`'s index words, `TX` gains `Σ rowsAt`. -/
theorem idxL_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ)
    (hng : R.gates.length < 2 ^ W) (hN : N < 2 ^ (R.r * R.s))
    (hKB : ∀ g ∈ R.gates, KeyBound (gateOf g) V) (hW : 2 * V + 3 ≤ W) (hnk : R.n + (starParamsOf R h).k + 4 ≤ W)
    (hcap : gateNeed (starParamsOf R h) W V ≤ cap) (hcap2 : 2 * W + 1 ≤ cap)
    (hcapG : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap) :
    ∀ (l : List ℕ) (σ : WState ns nr) (tx : ℕ) (pre rest : List Bool), Base S Q R h W V N σ →
      σ.st (S 31) = pre ++ idxWords W l ++ rest → σ.sh (S 31) = pre.length → NumOn σ (S 3) W tx →
      (∃ x, NumOn σ (S 44) W x) → (∃ j, NumOn σ (S 46) W j) → σ.val (Q 53) = l.length → l.length ≤ cap →
      (∀ i ∈ l, i < 2 ^ W) → tx + (l.map (rowsAt R h N)).sum < 2 ^ W →
      ∃ τ : WState ns nr, WExec cap (idxL S Q) σ τ
          (l.length * (1 + 1 + idxCost (starParamsOf R h) R.n W V R.gates.length + 2) + 1) ∧
        Base S Q R h W V N τ ∧ NumOn τ (S 3) W (tx + (l.map (rowsAt R h N)).sum) ∧
        τ.sh (S 31) = pre.length + l.length * (2 * W + 1) ∧ (∃ x, NumOn τ (S 44) W x) ∧
        (∃ j, NumOn τ (S 46) W j) ∧
        (∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 44 → k.val ≠ 46 → τ.st (S k) = σ.st (S k)) ∧
        (∀ k : Fin 50, k ≠ 31 → τ.sh (S k) = σ.sh (S k)) ∧ (∀ j : Fin 64, j ≠ 53 → τ.val (Q j) = σ.val (Q j)) ∧
        τ.val (Q 53) = 0 ∧ (∀ r : Fin nr, (∀ j : Fin 64, Q j ≠ r) → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | [], σ, tx, pre, rest, b, _, hPTh, hTX, hIX, hJ, h53, _, _, _ => by
    refine ⟨σ, WExec.cast cap (WExec.whrF (by rw [h53]; rfl)) rfl (by simp), b, by simpa using hTX, by simp [hPTh],
      hIX, hJ,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, by rw [h53]; rfl, fun _ _ => rfl, rfl⟩
  | i :: l, σ, tx, pre, rest, b, hPT, hPTh, hTX, hIX, hJ, h53, hlc, hil, hfit => by
    obtain ⟨x0, hx0⟩ := hIX
    obtain ⟨j0, hj0⟩ := hJ
    have hm : σ.val (Q 53) ≠ 0 := by rw [h53]; simp
    have d := WExec.dec (cap := cap) (Q 53) σ (by rw [h53]; exact hlc)
    set σ1 := σ.setv (Q 53) (σ.val (Q 53) - 1) with hσ1
    have b1 : Base S Q R h W V N σ1 := b.setv hS hQ 53 (by decide) _
    have hsum : (List.map (rowsAt R h N) (i :: l)).sum = rowsAt R h N i + (l.map (rowsAt R h N)).sum := by simp
    have hPT1 : σ1.st (S 31) = pre ++ frame (binary W i) ++ (idxWords W l ++ rest) := by
      simp [hσ1, hPT, idxWords]
    obtain ⟨τ1, x1, bτ1, hTX1, hPT1h, hIX1, hJ1, hst1, hsh1, hval1, hcell1⟩ := idxB_spec S hS Q hQ cap R h W V N σ1 b1
      i tx x0 j0 pre (idxWords W l ++ rest) hPT1 (by simp [hσ1, hPTh]) (numOn_setv _ _ _ _ _ _ hTX)
      (numOn_setv _ _ _ _ _ _ hx0) (numOn_setv _ _ _ _ _ _ hj0) (hil i (by simp)) hng hN hKB hW hnk
      (by rw [hsum] at hfit; omega) hcap hcap2 hcapG
    have hPTτ1 : τ1.st (S 31) = (pre ++ frame (binary W i)) ++ idxWords W l ++ rest := by
      rw [hst1 31 (by decide) (by decide) (by decide), hPT1]; simp
    obtain ⟨τ, x, bτ, hTXτ, hPTτ, hIXτ, hJτ, hstτ, hshτ, hvalτ, h53τ, hoτ, hcellτ⟩ := idxL_spec S hS Q hQ cap R h W V N
      hng hN hKB hW hnk hcap hcap2 hcapG l τ1 (tx + rowsAt R h N i) (pre ++ frame (binary W i)) rest bτ1 hPTτ1
      (by rw [hPT1h]; simp [RepairOrdinary.frame_length]; ring) hTX1 ⟨i, hIX1⟩ hJ1
      (by rw [hval1]; simp [hσ1, h53]) (by simp at hlc; omega) (fun j hj => hil j (by simp [hj]))
      (by rw [hsum] at hfit; omega)
    refine ⟨τ, ?_, bτ, by rw [hsum, ← Nat.add_assoc]; exact hTXτ, ?_, hIXτ, hJτ, ?_, ?_, ?_, h53τ, ?_, ?_⟩
    · refine WExec.cast cap (WExec.whrT hm (WExec.seq d x1) x) rfl ?_
      simp only [List.length_cons]
      ring_nf; omega
    · rw [hPTτ]; simp [RepairOrdinary.frame_length]; ring
    · intro k hk h44 h46
      rw [hstτ k hk h44 h46, hst1 k hk h44 h46]; rfl
    · intro k hk
      rw [hshτ k hk, hsh1 k hk]; rfl
    · intro j hj
      rw [hvalτ j hj, hval1]
      simp [hσ1, hQ.ne hj]
    · intro r hr
      rw [hoτ r hr, hval1]
      simp [hσ1, Function.update_apply, Ne.symm (hr 53)]
    · rw [hcellτ, hcell1]; rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
