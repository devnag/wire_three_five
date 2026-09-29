import Proof.Wire_3_5.Primitive.SeedFix.C4KWj

/-! # C4KW, part 11: the stage B1, run and cost

`b1P = b1Prog 98 17 90 stpB emsB` (the 17 rulers, the 90 emissions, the 17 erasures). From the stage's entry
(`st0'`: the inputs `1^ℓ₀, 1^t, 1^J, 1^G, 1^N, 1^{nE}, 1^{cap}, 1^{|pops|}` on streams `90 … 97`, every other stream
blank) **`b1_run'`** reaches the erasure invariant at `b1Cost 17 90 (Mb D cap)`; **`b1_le`** bounds the stage's
cost by `2·10⁶·(kwS + 1)² + 2·10⁶·(kwT + 1)⁶`; **`partB1 : PartB1`**: the 90 kept words `oB1 j` framed on the
outputs, the inputs kept, the scratch falses.

Paper quantity of the main type: the Hb printer's static words before cell `0` (P3:2253-2290), framed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B1
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4KW

noncomputable section

/-- **B1's word program.** -/
def b1P : WM 114 0 := b1Prog 98 17 90 stpB emsB

/-- The ruler bound. -/
def Mb (D : HashData) (cap : ℕ) : ℕ := 6 * (kwT D + 1) ^ 3 + cap

theorem ir0 (D : HashData) (cap : ℕ) :
    IR 90 98 (stIn (no := 90) iB1 D cap) (rvB D cap) stpB 0 (st0' (no := 90) iB1 D cap : WState 114 0) := by
  refine ⟨rfl, fun i hi => ⟨?_, rfl⟩, fun i _ _ => rfl, fun i _ _ _ => rfl, fun i h1 h2 => absurd h2 (by omega),
    fun i h1 => ⟨?_, rfl⟩⟩
  · show stIn (no := 90) iB1 D cap i = []
    unfold stIn; rw [dif_neg (by omega)]
  · show stIn (no := 90) iB1 D cap i = []
    unfold stIn; rw [dif_neg (by omega)]

theorem b1_run' (D : HashData) (cap : ℕ) :
    ∃ τ : WState 114 0, WExec 0 b1P (st0' (no := 90) iB1 D cap) τ (b1Cost 17 90 (Mb D cap)) ∧
      IX 90 98 (stIn (no := 90) iB1 D cap) (rvB D cap) emsB 17 τ :=
  b1_run 0 (stIn (no := 90) iB1 D cap) (rvB D cap) stpB emsB (Mb D cap) (by norm_num) (by norm_num) (stpB_ok D cap)
    emsB_ok (rvB_le D cap) _ (ir0 D cap)

theorem sq_split (x y : ℕ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  zify; nlinarith [sq_nonneg ((x : ℤ) - y)]

theorem b1_le (D : HashData) (cap : ℕ) :
    2 * b1Cost 17 90 (Mb D cap) + 2 ≤ 2000000 * (kwS D cap + 1) ^ 2 + 2000000 * (kwT D + 1) ^ 6 := by
  have hcap : cap + 1 ≤ kwS D cap + 1 := by unfold kwS; omega
  have hM : (Mb D cap + 1) ^ 2 ≤ 72 * (kwT D + 1) ^ 6 + 2 * (cap + 1) ^ 2 := by
    have e : Mb D cap + 1 = 6 * (kwT D + 1) ^ 3 + (cap + 1) := by unfold Mb; omega
    rw [e]
    have h1 := sq_split (6 * (kwT D + 1) ^ 3) (cap + 1)
    have e2 : 2 * (6 * (kwT D + 1) ^ 3) ^ 2 = 72 * (kwT D + 1) ^ 6 := by ring
    omega
  have hc2 : (cap + 1) ^ 2 ≤ (kwS D cap + 1) ^ 2 := Nat.pow_le_pow_left hcap 2
  have ha6 : 1 ≤ (kwT D + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold b1Cost
  omega

/-- **B1** (the rulers, the unary words, the constants, the registers, the log, the elimination's tapes). -/
def partB1 : PartB1 where
  x := 19
  s := _
  M := partM (no := 90) (ni := 8) (ns := 114) (nr := 0) (x := 19) (by norm_num) (by norm_num) b1P
  cost := fun D cap => 2 * b1Cost 17 90 (Mb D cap) + 2
  K := 2000000
  Dg := 6
  cost_le := b1_le
  run := fun D cap => by
    obtain ⟨τ, hw, hX⟩ := b1_run' D cap
    refine part_run (no := 90) (ni := 8) (ns := 114) (nr := 0) (x := 19) (by norm_num) (by norm_num) (by norm_num) oB1
      iB1 b1P D cap 0 τ (b1Cost 17 90 (Mb D cap)) hw hX.hcell (fun r => Fin.elim0 r) (Nat.zero_le _) (fun j => ?_)
      (fun k => ?_) (fun i hi => ?_)
    · exact (hX.hout ⟨j.val, by omega⟩ j.isLt).trans (congrArg frame (emsB_word D cap j))
    · have hk := k.isLt
      rw [hX.hinp _ (by simp) (by simp; omega)]
      unfold stIn
      rw [dif_pos (by simp; omega)]
      congr 2; apply Fin.ext; simp
    · have h1 := rvB_le D cap i
      have h2 : Mb D cap + 1 ≤ (Mb D cap + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      have h3 : Mb D cap = 6 * (kwT D + 1) ^ 3 + cap := rfl
      refine ⟨rvB D cap i + 1, ?_, hX.hera i hi (by omega)⟩
      unfold b1Cost
      omega

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B1
