import Proof.Wire_3_5.FinalPass.ThrPtRS23

/-! # S2 (THR per point), part 38: the machine's populations are the paper's (P3:2596-2606)

**`fast_pad`**: the list's fast report ignores trailing `0`s (`levelCount_pad`). **`selB_ofFn`**: the selected bits
are, occurrence by occurrence, `Z_i` when digit `d` of `a_i` is `1` — the digit population `thrDigitPop` of
row `(g, p)` (`digitPop` with `v_{i,d} ∈ {0, 1}`, radix `2`). Paper quantity: the digit lists `Z^±_{g,p,d}`
(P3:2598-2599) and their reports. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

theorem levelCount_pad (D : Lists.ListData) (j : ℕ) (Z : List Bool) (k : ℕ) :
    D.levelCount j (Z ++ List.replicate k false) = D.levelCount j Z := by
  unfold Lists.ListData.levelCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, List.length_append, List.length_replicate]
  constructor
  · rintro ⟨hi, h1, h2⟩
    by_cases hz : i < Z.length
    · refine ⟨hz, ?_, h2⟩
      rwa [List.getD_append _ _ _ _ hz] at h1
    · exfalso
      rw [List.getD_append_right _ _ _ _ (by omega)] at h1
      simp at h1
  · rintro ⟨hi, h1, h2⟩
    exact ⟨by omega, by rwa [List.getD_append _ _ _ _ hi], h2⟩

theorem fast_pad (D : Lists.ListData) (Z : List Bool) (k : ℕ) :
    ListFast.listReportFast D (Z ++ List.replicate k false) = ListFast.listReportFast D Z := by
  unfold ListFast.listReportFast ListFast.followed ListFast.decoded Lists.ListData.decoderBits
    Lists.ListData.levelDelta
  simp only [levelCount_pad]

theorem rep_mod2 (x : ℕ) (z : Bool) : List.replicate (x % 2) z = if x % 2 = 1 then [z] else [] := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- **The selected bits, occurrence by occurrence.** -/
theorem selB_ofFn (sgn : Bool) (d : ℕ) : ∀ (L : ℕ) (f : Fin L → ℕ) (Zf : Fin L → Bool) (X : List Bool),
    X.length = 4 * L → popBits sgn X = List.ofFn Zf →
    selB sgn d (List.ofFn f) X = (List.finRange L).flatMap fun i => if f i / 2 ^ d % 2 = 1 then [Zf i] else []
  | 0, _, _, _, _, _ => by simp [selB]
  | L + 1, f, Zf, b1 :: b2 :: b3 :: b4 :: X, hX, hZ => by
    have hX' : X.length = 4 * L := by simp at hX; omega
    rw [List.ofFn_succ] at hZ ⊢
    simp only [popBits, List.cons.injEq] at hZ
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    simp only [selB]
    rw [selB_ofFn sgn d L (fun i => f i.succ) (fun i => Zf i.succ) X hX' hZ.2]
    congr 2
    rw [← hZ.1]
    rfl
  | L + 1, _, _, [], hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | L + 1, _, _, [_], hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | L + 1, _, _, [_, _], hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | L + 1, _, _, [_, _, _], hX, _ => by simp only [List.length_cons, List.length_nil] at hX; omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
