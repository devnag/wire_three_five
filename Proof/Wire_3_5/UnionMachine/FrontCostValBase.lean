import Proof.Wire_3_5.UnionMachine.FrontCostC1

/-! # C6 front, the time (7): the valid path's cost at a guess (P3:3669-3691)

**`GF_le`**, **`PF_le`** (C1's request pieces grow with the variable count), **`nV_le`** (the numbers' registers
within `Z` when the grid, the mass, the counts and the data bound are), and **`validCost_le`**: at a guess with its
capacities (`PathCaps`, `EndCaps`) and its size envelope, and `n` above the width and the machine's polynomial
budgets, the valid path costs at most `C·n^D + 400·rOf + β`, `β` C1's call's budget.

Paper quantity of the main type: the valid path's time against the input length, the loop's capacity and C1's call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostVal
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit
open NearCubicWires.RepairRepresentation (natWord natListWord)

section Pieces
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb : ℕ)

theorem GF_le {x y : ℕ} (h : x ≤ y) : (C1Gates.GF Cs lits x).length ≤ (C1Gates.GF Cs lits y).length := by
  induction y, h using Nat.le_induction with
  | base => exact le_rfl
  | succ y _ ih =>
    refine ih.trans ?_
    show _ ≤ (C1Gates.GF Cs lits y ++ _).length
    rw [List.length_append]; omega

theorem PF_le {x y : ℕ} (h : x ≤ y) : (C1Gates.PF Cs lits cb x).length ≤ (C1Gates.PF Cs lits cb y).length := by
  induction y, h using Nat.le_induction with
  | base => exact le_rfl
  | succ y _ ih =>
    refine ih.trans ?_
    show _ ≤ (C1Gates.PF Cs lits cb y ++ _).length
    rw [List.length_append]; omega

end Pieces

section Regs
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The numbers' registers** stay within `Z`. -/
theorem nV_le (Kb Db : ℕ) (cdf : Bool) (Cδ q sys aux cb K Z : ℕ) (hq : q ≤ K) (hsys : sys ≤ K) (haux : aux ≤ K)
    (hcb : 2 ^ cb ≤ K) (hs : Ledger.rowBSparse h0 h1 2 Cδ q ≤ K) (hl : Ledger.rowBLambda h0 h1 2 q ≤ K)
    (hB : Kb * (q + 1) ^ Db ≤ Z) (hK : 2 * (K * K * K * K) + 2 * K + 1 ≤ Z) :
    ∀ r, FrontPw.nV h0 h1 Kb Db cdf Cδ q sys aux cb r ≤ Z := by
  have h := FrontPw.nV_out h0 h1 Kb Db cdf Cδ q sys aux cb
  have hLq : Ledger.Lq q ≤ q + 1 := Ledger.Lq_le q
  set s := Ledger.rowBSparse h0 h1 2 Cδ q
  set Λ := Ledger.rowBLambda h0 h1 2 q
  have k2 : K * K ≤ K * K * K * K := by
    rcases Nat.eq_zero_or_pos K with hk | hk
    · subst hk; simp
    · have : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (by positivity)
      calc K * K = K * K * 1 := by ring
        _ ≤ K * K * (K * K) := Nat.mul_le_mul_left _ this
        _ = K * K * K * K := by ring
  have hss : s * s * s * s ≤ K * K * K * K := by gcongr
  have hmb : Λ * Λ * (s * s) ≤ K * K * K * K := by
    calc Λ * Λ * (s * s) ≤ K * K * (K * K) := by gcongr
      _ = K * K * K * K := by ring
  have hmc : Λ * (s * s * s) ≤ K * K * K * K := by
    calc Λ * (s * s * s) ≤ K * (K * K * K) := by gcongr
      _ = K * K * K * K := by ring
  have hmd : Λ * Λ * Λ * s ≤ K * K * K * K := by gcongr
  have hme : Λ * Λ * Λ * Λ ≤ K * K * K * K := by gcongr
  have hsq : sys * q ≤ K * K := by gcongr
  have hee : sys * s + aux * s ≤ K * K + K * K := Nat.add_le_add (by gcongr) (by gcongr)
  intro r
  by_cases hr : r ∈ FrontTW.numKeep
  · simp only [FrontTW.numKeep, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.big]; exact hB
    · rw [h.cdf]; split_ifs <;> omega
    · rw [h.ss]; omega
    · rw [h.lam]; omega
    · rw [h.ll]; omega
    · rw [h.qq]; omega
    · rw [h.sy]; omega
    · rw [h.sq]; omega
    · rw [h.mm]; omega
    · rw [h.ee]; omega
    · rw [h.ma]; omega
    · rw [h.mb]; omega
    · rw [h.mc]; omega
    · rw [h.md]; omega
    · rw [h.me]; omega
    · rw [h.mf]; omega
    · rw [h.ok]; omega
  · rw [h.zero r hr]; exact Nat.zero_le _

end Regs

/-- The capacity sum's parts. -/
theorem capR_parts (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 T : ℕ)
    (h : a1 + a2 + a3 + 6 * a4 + 8 + a5 + a6 + a7 + 2 * a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + 6 * a17 +
      6 * a18 + 40 ≤ T) :
    a7 ≤ T ∧ a10 ≤ T ∧ a8 ≤ T ∧ a9 ≤ T ∧ a11 ≤ T ∧ a13 ≤ T ∧ a15 ≤ T ∧ a16 ≤ T := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

section Guess
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.RepairOrdinary.Streaming (marks)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The carrier loop's total. -/
theorem mulc_le (a b n : ℕ) (hn : 1 ≤ n) (ha : a ≤ n) (hb : b ≤ 10 ^ 12 * n ^ 6) : a * (b + 2) ≤ 10 ^ 13 * n ^ 40 := by
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostVal
