import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR7

/-! # THR decode front, RADIX part 7b: the post-dock facts

The values `tCW` leaves (`tCOut_rs`, `tCOut_nc`, `tCOut_cap`, `tCOut_a`, `tCOut_other`), the blocks `G`, `H` as
clear lists (`gList`, `hList`), and the data tape's read position against the rewind count (`sh113_le`).

Paper quantity of the main types: the RADIX setup's entry registers (`RsIn4.vals`, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

/-- The block `G` (`408 … 471`). -/
def gList : List (Fin LNR) := (List.finRange 64).map G

/-- The block `H` (`472 … 511`). -/
def hList : List (Fin LNR) := (List.finRange 40).map H

theorem gList_length : gList.length = 64 := by simp [gList]
theorem hList_length : hList.length = 40 := by simp [hList]

theorem mem_gList (q : Fin LNR) (h1 : 408 ≤ q.val) (h2 : q.val < 472) : q ∈ gList := by
  unfold gList; rw [List.mem_map]
  exact ⟨⟨q.val - 408, by omega⟩, List.mem_finRange _, Fin.ext (by rw [G_val]; simp only; omega)⟩

theorem not_mem_gList (q : Fin LNR) (h : q.val < 408 ∨ 472 ≤ q.val) : q ∉ gList := by
  unfold gList; rw [List.mem_map]
  rintro ⟨i, -, hi⟩
  have := congrArg Fin.val hi; rw [G_val] at this; have := i.isLt; omega

theorem mem_hList (q : Fin LNR) (h1 : 472 ≤ q.val) : q ∈ hList := by
  have hq : q.val < 512 := q.isLt
  unfold hList; rw [List.mem_map]
  exact ⟨⟨q.val - 472, by omega⟩, List.mem_finRange _, Fin.ext (by rw [H_val]; simp only; omega)⟩

theorem not_mem_hList (q : Fin LNR) (h : q.val < 472) : q ∉ hList := by
  unfold hList; rw [List.mem_map]
  rintro ⟨i, -, hi⟩
  have := congrArg Fin.val hi; rw [H_val] at this; omega

section R7b
variable (x : ℕ)

theorem tCOut_other (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) (r : Fin LNR)
    (hr : r.val < 410 ∨ 432 < r.val) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).val r = σ.val r := by
  have e0 : r.val ≠ 410 := by omega
  have e1 : r.val ≠ 411 := by omega
  have e2 : r.val ≠ 412 := by omega
  have e3 : r.val ≠ 413 := by omega
  have e4 : r.val ≠ 414 := by omega
  have e5 : r.val ≠ 415 := by omega
  have e6 : r.val ≠ 416 := by omega
  have e7 : r.val ≠ 417 := by omega
  have e8 : r.val ≠ 418 := by omega
  have e9 : r.val ≠ 419 := by omega
  have e10 : r.val ≠ 420 := by omega
  have e11 : r.val ≠ 421 := by omega
  have e12 : r.val ≠ 422 := by omega
  have e13 : r.val ≠ 423 := by omega
  have e14 : r.val ≠ 424 := by omega
  have e15 : r.val ≠ 425 := by omega
  have e16 : r.val ≠ 426 := by omega
  have e17 : r.val ≠ 427 := by omega
  have e18 : r.val ≠ 428 := by omega
  have e19 : r.val ≠ 429 := by omega
  have e20 : r.val ≠ 430 := by omega
  have e21 : r.val ≠ 431 := by omega
  have e22 : r.val ≠ 432 := by omega
  unfold tCOut
  simp [Function.update_apply, Fin.ext_iff, PrimThrW.RadSetup.rsReg, PrimThrW.RadSetup2.rNcK,
    PrimThrW.RadSetup2.rCapK, RadSetupB2.rAK, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22]

theorem tCOut_rs (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) (i : Fin 20) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).val (PrimThrW.RadSetup.rsReg i) =
      (![gi, p, s, row, 2 * (xa + xb) + mo, 2 * (xa + xb), n, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v14,
        v15] : Fin 20 → ℕ) i := by
  unfold tCOut
  fin_cases i <;> simp [Function.update_apply, Fin.ext_iff, PrimThrW.RadSetup.rsReg, PrimThrW.RadSetup2.rNcK,
    PrimThrW.RadSetup2.rCapK, RadSetupB2.rAK]

theorem tCOut_nc (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).val PrimThrW.RadSetup2.rNcK = v0 := by
  unfold tCOut
  simp [Function.update_apply, Fin.ext_iff, PrimThrW.RadSetup.rsReg, PrimThrW.RadSetup2.rNcK,
    PrimThrW.RadSetup2.rCapK, RadSetupB2.rAK]

theorem tCOut_cap (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).val PrimThrW.RadSetup2.rCapK = v1 := by
  unfold tCOut
  simp [Function.update_apply, Fin.ext_iff, PrimThrW.RadSetup.rsReg, PrimThrW.RadSetup2.rNcK,
    PrimThrW.RadSetup2.rCapK, RadSetupB2.rAK]

theorem tCOut_a (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).val RadSetupB2.rAK = a := by
  unfold tCOut
  simp [Function.update_apply, Fin.ext_iff, PrimThrW.RadSetup.rsReg, PrimThrW.RadSetup2.rNcK,
    PrimThrW.RadSetup2.rCapK, RadSetupB2.rAK]

theorem tCOut_st (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).st = σ.st := by unfold tCOut; simp
theorem tCOut_sh (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).sh = σ.sh := by unfold tCOut; simp
theorem tCOut_cell (σ : WState (LNS x) LNR) (gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    (tCOut x σ gi p s row xa xb mo n a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).cell = σ.cell := by unfold tCOut; simp

end R7b

theorem sum16 (hs : List ℕ) (hhs : hs.length = 16) :
    hs.sum = hs.getD 0 0 + hs.getD 1 0 + hs.getD 2 0 + hs.getD 3 0 + hs.getD 4 0 + hs.getD 5 0 + hs.getD 6 0 +
      hs.getD 7 0 + hs.getD 8 0 + hs.getD 9 0 + hs.getD 10 0 + hs.getD 11 0 + hs.getD 12 0 + hs.getD 13 0 +
      hs.getD 14 0 + hs.getD 15 0 := by
  have h := sum_fin_getD hs 16 (by omega)
  rw [List.take_of_length_le (by omega)] at h
  rw [← h]
  simp [Fin.sum_univ_succ]
  omega

theorem sum_le2 (xs : List ℕ) (hxs : xs.length ≤ 2) : xs.sum = xs.getD 0 0 + xs.getD 1 0 := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp
  · simp
  · simp
  · simp at hxs

/-- **The data tape's read position** after the numbers phase, as the rewind count's sum. -/
theorem sh113_eq (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2) :
    (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length =
      hs.sum + (xs.getD 0 0 + xs.getD 1 0) + 16 + xs.length := by
  have e : (hs ++ (xs ++ [tg])).take (16 + xs.length) = hs ++ xs := by
    rw [show 16 + xs.length = hs.length + xs.length by omega, List.take_append,
      List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.take_left' rfl]
  rw [e, unaryList_length_le, List.sum_append, List.length_append, sum_le2 xs hxs]
  omega

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
