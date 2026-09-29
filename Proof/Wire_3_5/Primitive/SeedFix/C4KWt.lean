import Proof.Wire_3_5.Primitive.SeedFix.C4KWs

/-! # C4KW, part 19: stage B2's run

**`b2_core`**: from B2's entry (`st0'`: `1^t, 1^J, 1^{B*}` on streams `1 2 3`), the setup, the levels and the
teardown leave `outL (J+1) ++ [false]` on the output, the inputs kept, the words falses, every register `0`.

Paper quantity of the main type: the cleared weights' word `wtWord (wsOf MP)` (P3:2280-2281), framed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.UnionMachine.EwLevel (twOf twMax twOf_le twCost)

/-- **B2's run.** -/
theorem b2_core (D : C4H.HashData) (cap : ℕ) :
    ∃ τ : WState 5 48, WExec (capB D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar) b2P
      (st0' (no := 1) iB2 D cap) τ (b2Cost D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J D.MP.Bstar) ∧
      τ.cell = false ∧ (∀ r, τ.val r = 0) ∧
      τ.st 0 = outL D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J (D.MP.J + 1) ++ [false] ∧
      (∀ i : Fin 6, i ≠ 0 → i ≠ sP → i ≠ sC → τ.st i = (st0' (no := 1) iB2 D cap : WState 5 48).st i) ∧
      τ.st sP = List.replicate (2 * wdOf D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J + 1) false ∧
      τ.st sC = List.replicate (2 * wdOf D.MP.t (Nat.sqrt (D.MP.t * D.MP.Bstar)) D.MP.J + 1) false := by
  set t := D.MP.t with ht
  set J := D.MP.J with hJ
  set B := D.MP.Bstar with hB
  set s := Nat.sqrt (t * B) with hs
  set σ0 : WState 5 48 := st0' (no := 1) iB2 D cap with hσ0
  set cp := capB t s J B with hcp
  have hv0 : ∀ r, σ0.val r = 0 := fun _ => rfl
  have hsh0 : ∀ i, σ0.sh i = 0 := fun _ => rfl
  have t1 := setup_run cp σ0 t J B hv0 hsh0 rfl rfl rfl rfl rfl le_rfl
  have g1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have hsle : s ≤ t * B := Nat.sqrt_le_self _
  have hwd1 : 1 ≤ wdOf t s J := by unfold wdOf; omega
  have hcapL : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 2 * wdOf t s J + 2 * t + twMax t s + 10 ≤ cp := by
    rw [hcp]; unfold capB
    generalize 2 * (B * t + 2) * (B * t + 2) = Q
    generalize B * t = R
    generalize 2 ^ (J + 1) = P at g1 ⊢
    omega
  obtain ⟨τ, t2, hτ⟩ := l_loop cp (outC σ0 t J B s) (wdOf t s J) t s J (b2_in σ0 t J B s hv0 hsh0 rfl) (pow_lt_wd t s J) hwd1 hcapL
    (J + 1) 0 (outC σ0 t J B s) (by omega) (b2_rl0 σ0 t J B s hv0 hsh0 rfl)
  obtain ⟨τf, t3, hc, hv, h0, hst, hP, hC⟩ := tear_run σ0 t J B s hv0 hsh0 rfl cp τ hτ (by
    rw [hcp]; unfold capB
    generalize 2 * (B * t + 2) * (B * t + 2) = Q
    generalize B * t = R
    generalize 2 ^ (J + 1) = P
    omega)
  refine ⟨τf, WExec.seq t1 (WExec.seq t2 t3), by rw [hc, hτ.cl]; rfl, hv, ?_, fun i h1 h2 h3 => ?_, hP, hC⟩
  · rw [h0, hτ.O, outC_st σ0 t J B s hv0]; rfl
  · rw [hst i h1 h2 h3, hτ.st i h1 h2 h3, outC_st σ0 t J B s hv0, if_neg h3, if_neg h2]

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
