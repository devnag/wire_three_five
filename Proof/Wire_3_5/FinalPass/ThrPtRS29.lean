import Proof.Wire_3_5.FinalPass.ThrPtRS28

/-! # S2 (THR per point), part 43: the call's entry read internally (P3:3170-3178)

For a THR call `k` and a `PtIn2` entry `σ` at `thrWords k`, `thrNums k`: **`init_of`** (`view0 σ` is the internal entry
`Init0` with `a, |𝒢|, τ₀, |occs|`), the call's words on the internal streams (`thrWords_pay`, `thrWords_primes`,
`thrWords_level`, `view0_st`), and the table's width facts (**`table_facts`**). Paper quantity: the call's data
(the tuple's table, payloads, primes, stage 4's table). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline

theorem thrWords_pay (k : Seams.ThrCall) (i : Fin 4) :
    Seams.thrWords k ⟨i.val + 1, by omega⟩ =
      if h : i.val < k.a then PrimThrW.TopFront.payOf k.alg (k.Cs ⟨i.val, h⟩) else [] := by
  unfold Seams.thrWords
  have hi := i.isLt
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  by_cases h : i.val < k.a
  · rw [dif_pos ⟨h, by omega⟩, dif_pos h]
  · rw [dif_neg (fun h' => h h'.1), dif_neg h, if_pos (by omega)]

theorem thrWords_primes (k : Seams.ThrCall) :
    Seams.thrWords k 5 = PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (Primitive.thrCutoff k.P k.Cs k.alg k.den)) := by
  unfold Seams.thrWords
  simp

theorem thrWords_level (k : Seams.ThrCall) :
    Seams.thrWords k 6 =
      ListEval.levelWord k.D.M k.D.J k.D.W (ListEval.rowsOf k.D (Primitive.thrOccs k.P k.Cs).length) := by
  unfold Seams.thrWords
  simp

theorem thrWords_table (k : Seams.ThrCall) :
    Seams.thrWords k 0 =
      if k.a = 0 then [] else Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG k.Cs)) (PrimT.ThrTab.tupleG k.Cs) := by
  unfold Seams.thrWords
  simp

section View
variable {ns nr : ℕ} (S : Fin 3 ⊕ Fin 7 ⊕ Fin 7 ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin 4 ⊕ Fin 113 ↪ Fin nr)

theorem view0_st (σ : WState ns nr) (j : Fin 17) (h : j.val < 10) : (view0 S R σ).st j = σ.st (S (sOf j)) := by
  show (if 10 ≤ j.val then [] else σ.st (fS S j)) = _
  rw [if_neg (by omega)]
  rfl

theorem rOf_scr (q : Fin 118) (h0 : q.val ≠ 0) (h5 : q.val ≠ 5) (h8 : q.val ≠ 8) (h63 : q.val ≠ 63)
    (h109 : q.val ≠ 109) : rOf q = .inr (.inr ⟨sIdx q.val, sIdx_lt q⟩) := by
  unfold rOf
  rw [if_neg h0, if_neg h5, if_neg h109, if_neg h8, if_neg h63]

/-- **The call's entry, read internally, is `Init0`.** -/
theorem init_of (k : Seams.ThrCall) (c : BitInput k.P.n) (u v : k.P.Errors) (σ : WState ns nr)
    (hin : Seams.PtIn2 S R c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (Seams.thrWords k)
      (Seams.thrNums k) σ) :
    Init0 (view0 S R σ) k.a (Fintype.card (Primitive.ThrEq k.P k.Cs k.alg)) (Primitive.thrDigits k.P k.Cs k.alg k.den)
      (Primitive.thrOccs k.P k.Cs).length where
  sh := fun j => hin.1.heads (sOf j)
  cell := hin.2
  s10 := rfl
  s11 := rfl
  s12 := rfl
  s13 := rfl
  s14 := rfl
  s15 := rfl
  s16 := rfl
  v0 := hin.1.acc
  v5 := hin.1.num 0
  v8 := hin.1.num 2
  v63 := hin.1.num 3
  v109 := hin.1.num 1
  zero := fun q h0 h5 h8 h63 h109 => by
    show σ.val (R (rOf q)) = 0
    rw [rOf_scr q h0 h5 h8 h63 h109]
    exact hin.1.zero _

end View

/-- **The width measurement's facts on the call's table.** -/
theorem table_facts (k : Seams.ThrCall) :
    (∀ i < thrH k.Cs, readTapeBit (Seams.thrWords k 0) (1 + 2 * i) = true) ∧
      readTapeBit (Seams.thrWords k 0) (1 + 2 * thrH k.Cs) = false ∧
      (k.a ≠ 0 → Seams.thrWords k 0 = Corner.gatesW (thrH k.Cs) (PrimT.ThrTab.tupleG k.Cs)) := by
  rw [thrWords_table]
  by_cases ha : k.a = 0
  · have hG := tupleG_zero k.P k.Cs ha
    have hH : thrH k.Cs = 0 := by unfold thrH; rw [if_pos hG]
    rw [if_pos ha, hH]
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), by simp [readTapeBit], fun h => absurd ha h⟩
  · rw [if_neg ha, gatesW_thrH]
    refine ⟨?_, ?_, fun _ => rfl⟩
    · cases hG : PrimT.ThrTab.tupleG k.Cs with
      | nil =>
        have hH : thrH k.Cs = 0 := by unfold thrH; rw [if_pos hG]
        intro i hi
        rw [hH] at hi
        exact absurd hi (Nat.not_lt_zero _)
      | cons g G => exact (table_read (thrH k.Cs) g G).1
    · cases hG : PrimT.ThrTab.tupleG k.Cs with
      | nil =>
        have hH : thrH k.Cs = 0 := by unfold thrH; rw [if_pos hG]
        rw [hH]
        rfl
      | cons g G => exact (table_read (thrH k.Cs) g G).2

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
