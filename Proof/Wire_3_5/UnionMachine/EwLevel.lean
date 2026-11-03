import Proof.Wire_3_5.UnionMachine.EwKit
import Proof.Wire_3_5.FinalPass.ListEvalRef

/-! # C6, e/W_j, part 2: one level's window and its power

"`W_j = 16t + 20(⌊√(t·B_*)⌋ + 1)/2^{⌊j/2⌋} + 20`" (filt:majorant, P3:2150-2157; `Filters.MajorantParams.W`) and the
level record's power `2^{⌈log₂(2W_j+1)⌉}` (`FinalPass.ListEval.pow`). From `t`, `s = ⌊√(t·B_*)⌋` and the level `j` in
registers (kept): **`twW`** / **`twW_spec`** (`TW := 16t + 20((s+1)/2^{⌊j/2⌋} + 1)`; PA's `pow2W`, `divW`), then
`EwKit.powF` (**`lvVal_spec`**: both, the scratch back at `0`). Costs in the values.

Paper quantity: the fixed hash's level window `W_j` and its power (filt:majorant). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwLevel
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR halveR bsetv_self)

variable {ns nr : ℕ} (cap : ℕ)

/-- `pow2W`'s registers: exponent `11`, out `4`, temps `12`, `13`. -/
def pwE : Fin 4 ↪ Fin 20 := ⟨![11, 4, 12, 13], by decide⟩
/-- `divW`'s registers: numerator `5`, divisor `4`, quotient `6`, temps `12 … 17`. -/
def dvE : Fin 9 ↪ Fin 20 := ⟨![5, 4, 6, 12, 13, 14, 15, 16, 17], by decide⟩
/-- `powF`'s registers: window `7`, power `8`, temps `12 … 14`. -/
def pfE : Fin 5 ↪ Fin 20 := ⟨![7, 8, 12, 13, 14], by decide⟩

@[simp] theorem pwE_apply (i : Fin 4) : pwE i = ![11, 4, 12, 13] i := rfl
@[simp] theorem dvE_apply (i : Fin 9) : dvE i = ![5, 4, 6, 12, 13, 14, 15, 16, 17] i := rfl
@[simp] theorem pfE_apply (i : Fin 5) : pfE i = ![7, 8, 12, 13, 14] i := rfl

section Level
variable (V : Fin 20 ↪ Fin nr)

/-- **The level window** `TW := 16t + 20((s+1)/2^{⌊j/2⌋} + 1)` (`V 0 = t`, `V 1 = s`, `V 2 = j` kept; out `V 7`). -/
def twW : WM ns nr :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (dupR (V 2) (V 3) (V 10)) (halveR (V 3) (V 11) (V 9))) (WM.clear (V 9))) (PrimAsm.UnaryArith.pow2W (pwE.trans V)))
    (dupR (V 1) (V 5) (V 10))) (.inc (V 5))) (PrimAsm.UnaryArith.divW (dvE.trans V))) (WM.clear (V 5)))
    (WM.clear (V 4))) (WM.clear (V 11))) (FsKit.mulK (V 0) (V 7) (V 10) 16)) (.inc (V 6)))
    (FsKit.mulK (V 6) (V 7) (V 10) 20)) (WM.clear (V 6))

/-- The level window's value. -/
def twOf (t s j : ℕ) : ℕ := 16 * t + 20 * ((s + 1) / 2 ^ (j / 2) + 1)

/-- A bound on the level window's cost. -/
def twCost (t s j : ℕ) : ℕ := 2000 * (t + s + j + 2 ^ j + 2) * (t + s + j + 2 ^ j + 2)

theorem twW_spec (σ : WState ns nr) (t s j : ℕ) (h0 : σ.val (V 0) = t) (h1 : σ.val (V 1) = s)
    (h2 : σ.val (V 2) = j) (hz : ∀ i : Fin 20, 3 ≤ i.val → σ.val (V i) = 0)
    (hcap : 2 ^ (j + 1) + j + s + 1000 * (t + s + 2) ≤ cap) :
    ∃ n, WExec cap (twW V) σ (σ.setv (V 7) (twOf t s j)) n ∧ n ≤ twCost t s j := by
  have hne : ∀ {i k : Fin 20}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have hV : ∀ i k : Fin 20, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have z3 := hz 3 (by decide)
  have z4 := hz 4 (by decide)
  have z5 := hz 5 (by decide)
  have z6 := hz 6 (by decide)
  have z7 := hz 7 (by decide)
  have z8 := hz 8 (by decide)
  have z9 := hz 9 (by decide)
  have z10 := hz 10 (by decide)
  have z11 := hz 11 (by decide)
  have z12 := hz 12 (by decide)
  have z13 := hz 13 (by decide)
  have z14 := hz 14 (by decide)
  have z15 := hz 15 (by decide)
  have z16 := hz 16 (by decide)
  have z17 := hz 17 (by decide)
  obtain ⟨D, hD⟩ : ∃ D, D = 2 ^ (j / 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (s + 1) / D := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ Rm, Rm = (s + 1) % D := ⟨_, rfl⟩
  have hj2 : j / 2 ≤ j := Nat.div_le_self _ _
  have hDj : D ≤ 2 ^ j := by rw [hD]; exact Nat.pow_le_pow_right (by norm_num) hj2
  have hpj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_two_pow
  have hQs : Q ≤ s + 1 := by rw [hQ]; exact Nat.div_le_self _ _
  have hRD : Rm < D := by rw [hRm]; exact Nat.mod_lt _ (by omega)
  have hpe : 2 ^ (j / 2 + 1) = 2 * D := by rw [hD, pow_succ]; ring
  have hje : j / 2 < D := by rw [hD]; exact Nat.lt_two_pow_self
  have c1 := BinW.dupR_spec cap (V 2) (V 3) (V 10) (hne (by decide)) (hne (by decide)) (hne (by decide)) σ j h2
    z3 z10 (by omega)
  have c2 := WExec.seq c1 (BinW.halve_spec cap (V 3) (V 11) (V 9) (hne (by decide)) (hne (by decide))
    (hne (by decide)) j _ (by simp) (by omega) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by omega))
  have c3 := WExec.seq c2 (wclear_spec cap (V 9) (j % 2) _ (by simp) (by simp; omega))
  have c4 := WExec.seq c3 (PrimAsm.UnaryArith.pow2W_spec cap (pwE.trans V) _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm])
    (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  have c5 := WExec.seq c4 (BinW.dupR_spec cap (V 1) (V 5) (V 10) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ s (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by omega))
  have c6 := WExec.seq c5 (WExec.inc (cap := cap) (V 5) _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  have c7 := WExec.seq c6 (PrimAsm.UnaryArith.divW_spec cap (dvE.trans V) _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega)
    (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega)
    (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega) (by omega))
  have c8 := WExec.seq c7 (wclear_spec cap (V 5) Rm _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  have c9 := WExec.seq c8 (wclear_spec cap (V 4) D _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  have c10 := WExec.seq c9 (wclear_spec cap (V 11) (j / 2) _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  have c11 := WExec.seq c10 (FsKit.mulK_spec cap (V 0) (V 7) (V 10) (hne (by decide)) (hne (by decide))
    (hne (by decide)) t 16 _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega) (by omega))
  have c12 := WExec.seq c11 (WExec.inc (cap := cap) (V 6) _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  have c13 := WExec.seq c12 (FsKit.mulK_spec cap (V 6) (V 7) (V 10) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (Q + 1) 20 _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega) (by omega))
  have c14 := WExec.seq c13 (wclear_spec cap (V 6) (Q + 1) _ (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]) (by simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]; omega))
  refine ⟨_, WExec.cast cap c14 ?_ le_rfl, ?_⟩
  · clear c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14
    apply WState.eq
    · simp
    · simp
    · funext r
      by_cases r7 : r = V 7
      · subst r7; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm, twOf] <;> omega
      · by_cases r3 : r = V 3
        · subst r3; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
        · by_cases r4 : r = V 4
          · subst r4; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
          · by_cases r5 : r = V 5
            · subst r5; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
            · by_cases r6 : r = V 6
              · subst r6; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
              · by_cases r9 : r = V 9
                · subst r9; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
                · by_cases r11 : r = V 11
                  · subst r11; simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
                  · simp [Function.update_apply, r3, r4, r5, r6, r7, r9, r11]
    · simp
  · clear c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14
    simp [hV, h0, h1, h2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, ← hD, ← hQ, ← hRm]
    unfold twCost
    obtain ⟨X, hX⟩ : ∃ X, X = t + s + j + 2 ^ j + 2 := ⟨_, rfl⟩
    rw [← hX]
    have hX2 : 2 ≤ X := by omega
    have hXX : X ≤ X * X := Nat.le_mul_self X
    have hDX : D ≤ X := by omega
    have hA : (s + 1 + 2) * (90 * (s + 1) + 90 * D + 60) ≤ X * (300 * X) := Nat.mul_le_mul (by omega) (by omega)
    have hB : j / 2 * (18 * D + 7) ≤ X * (25 * X) := Nat.mul_le_mul (by omega) (by omega)
    have hj2' : j % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    nlinarith

end Level

/-! ## Appending ones -/

section Ones
variable (O : Fin (ns + 1)) (A P : Fin nr)

/-- The ones loop: append `1^a` to `O` (counting in `P`), `A := 0`. -/
def onesL : WM ns nr := .whr A (.seq (.dec A) (emitC O P true))

/-- The state after `i` ones appended to `w` (head at the end, count `c + i`). -/
def stA (σ : WState ns nr) (w : List Bool) (c a i : ℕ) : WState ns nr :=
  (((σ.sets O (w ++ List.replicate i true)).seth O (w.length + i)).setv A (a - i)).setv P (c + i)

theorem onesL_spec (hAP : A ≠ P) (σ : WState ns nr) (w : List Bool) (c a : ℕ) (hcap : c + a + 1 ≤ cap)
    (hcap2 : a ≤ cap) : ∀ j i : ℕ, i + j = a →
      WExec cap (onesL O A P) (stA O A P σ w c a i) (stA O A P σ w c a a) (j * 11 + 1)
  | 0, i, h => by
    have hi : i = a := by omega
    subst hi
    exact WExec.whrF (by simp [stA, hAP])
  | j + 1, i, h => by
    have h1 := WExec.dec (cap := cap) A (stA O A P σ w c a i) (by simp [stA, hAP]; omega)
    have hO : ((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)).sh O =
        (((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)).st O).length := by simp [stA]
    have h2 := emitC_spec cap O P true ((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)) hO
      (by simp [stA, Ne.symm hAP]; omega)
    have ih := onesL_spec hAP σ w c a hcap hcap2 j (i + 1) (by omega)
    have e : (((((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)).sets O
        (((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)).st O ++ [true])).seth O
        (((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)).sh O + 1)).setv P
        (((stA O A P σ w c a i).setv A ((stA O A P σ w c a i).val A - 1)).val P + 1)) = stA O A P σ w c a (i + 1) := by
      apply WState.eq
      · funext k
        by_cases hk : k = O
        · subst hk; simp [stA]; omega
        · simp [stA, hk]
      · funext k
        by_cases hk : k = O
        · subst hk; simp [stA, ← List.replicate_succ']
        · simp [stA, hk]
      · funext k
        simp only [stA, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
        by_cases hkP : k = P
        · subst hkP; simp [Ne.symm hAP]; omega
        · by_cases hkA : k = A
          · subst hkA; simp [hkP]; omega
          · simp [hkP, hkA]
      · rfl
    rw [e] at h2
    refine WExec.mono (WExec.whrT (by simp [stA, hAP]; omega) (WExec.seq h1 h2) ih) ?_
    have e2 : (j + 1) * 11 = j * 11 + 11 := by ring
    rw [e2]; omega

end Ones

theorem ones_spec (O : Fin (ns + 1)) (A P : Fin nr) (hAP : A ≠ P) (σ : WState ns nr) (w : List Bool) (c a : ℕ)
    (hw : σ.st O = w) (hh : σ.sh O = w.length) (hc : σ.val P = c) (ha : σ.val A = a) (hcap : c + a + 1 ≤ cap) :
    WExec cap (onesL O A P) σ ((((σ.sets O (w ++ List.replicate a true)).seth O (w.length + a)).setv A 0).setv P
      (c + a)) (a * 11 + 1) := by
  have h := onesL_spec cap O A P hAP σ w c a hcap (by omega) a 0 (by omega)
  have e0 : stA O A P σ w c a 0 = σ := by
    apply WState.eq
    · funext k
      by_cases hk : k = O
      · subst hk; simp [stA, hh]
      · simp [stA, hk]
    · funext k
      by_cases hk : k = O
      · subst hk; simp [stA, hw]
      · simp [stA, hk]
    · funext k
      simp only [stA, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      by_cases hkP : k = P
      · subst hkP; simp [hc]
      · by_cases hkA : k = A
        · subst hkA; simp [hkP, ha]
        · simp [hkP, hkA]
    · rfl
  rw [e0] at h
  refine WExec.cast cap h ?_ le_rfl
  simp [stA]

section Rec
variable (O : Fin (ns + 1)) (PC : Fin nr) (V : Fin 20 ↪ Fin nr)

/-- **One level record**: append `true :: (unary P ++ unary TW)` (`P = V 8`, `TW = V 7` kept) to `O`. -/
def recE : WM ns nr :=
  .seq (.seq (.seq (.seq (.seq (.seq (emitC O PC true) (dupR (V 8) (V 12) (V 10))) (onesL O (V 12) PC))
    (emitC O PC false)) (dupR (V 7) (V 12) (V 10))) (onesL O (V 12) PC)) (emitC O PC false)

theorem recE_spec (hPC : ∀ i, V i ≠ PC) (σ : WState ns nr) (w : List Bool) (c p tw : ℕ) (hw : σ.st O = w)
    (hh : σ.sh O = w.length) (hc : σ.val PC = c) (h7 : σ.val (V 7) = tw) (h8 : σ.val (V 8) = p)
    (h10 : σ.val (V 10) = 0) (h12 : σ.val (V 12) = 0) (hcap : c + p + tw + 10 ≤ cap) :
    WExec cap (recE O PC V) σ (((σ.sets O (w ++ (true :: (FinalPass.ListEval.unary p ++
      FinalPass.ListEval.unary tw)))).seth O (w.length + (p + tw + 3))).setv PC (c + (p + tw + 3)))
      (40 * (p + tw) + 80) := by
  have hne : ∀ {i k : Fin 20}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have hV : ∀ i k : Fin 20, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hP' : ∀ i, PC ≠ V i := fun i h => hPC i h.symm
  have c1 := emitC_spec cap O PC true σ (by rw [hh, hw]) (by omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap (V 8) (V 12) (V 10) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ p (by simp [h8, hPC]) (by simp [h12, hPC]) (by simp [h10, hPC]) (by omega))
  have c3 := WExec.seq c2 (ones_spec cap O (V 12) PC (hPC 12) _ (w ++ [true]) (c + 1) p (by simp [hw])
    (by simp [hh]) (by simp [hc, hP']) (by simp) (by omega))
  have c4 := WExec.seq c3 (emitC_spec cap O PC false _ (by simp <;> omega) (by simp; omega))
  have c5 := WExec.seq c4 (BinW.dupR_spec cap (V 7) (V 12) (V 10) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ tw (by simp [h7, hPC, hV]) (by simp [hPC]) (by simp [h10, hPC, hV]) (by omega))
  have c6 := WExec.seq c5 (ones_spec cap O (V 12) PC (hPC 12) _ (w ++ [true] ++ List.replicate p true ++ [false])
    (c + 1 + p + 1) tw (by simp) (by simp; omega) (by simp [hP']) (by simp) (by omega))
  have c7 := WExec.seq c6 (emitC_spec cap O PC false _ (by simp <;> omega) (by simp; omega))
  refine WExec.cast cap c7 ?_ (by omega)
  clear c1 c2 c3 c4 c5 c6 c7
  apply WState.eq
  · funext k
    by_cases hk : k = O
    · subst hk; simp; omega
    · simp [hk]
  · funext k
    by_cases hk : k = O
    · subst hk; simp [FinalPass.ListEval.unary]
    · simp [hk]
  · funext k
    by_cases hkP : k = PC
    · subst hkP; simp [hP']; omega
    · by_cases hk12 : k = V 12
      · subst hk12; simp [hPC, h12]
      · simp [Function.update_apply, hkP, hk12]
  · simp

end Rec

/-! ## The levels below the top -/

/-- The record of level `j` (`W_j` from `t` and `s = ⌊√(tB)⌋`). -/
def recOf (t s j : ℕ) : List Bool :=
  true :: (FinalPass.ListEval.unary (2 ^ Nat.clog 2 (2 * twOf t s j + 1)) ++ FinalPass.ListEval.unary (twOf t s j))

/-- The records of the levels `J − 1, …, J − k`. -/
def recsDown (t s J : ℕ) (k : ℕ) : List Bool := (List.range k).flatMap fun i => recOf t s (J - 1 - i)

theorem recsDown_succ (t s J k : ℕ) : recsDown t s J (k + 1) = recsDown t s J k ++ recOf t s (J - 1 - k) := by
  simp [recsDown, List.range_succ, List.flatMap_append]

theorem recOf_length (t s j : ℕ) :
    (recOf t s j).length = 2 ^ Nat.clog 2 (2 * twOf t s j + 1) + twOf t s j + 3 := by
  simp [recOf, FinalPass.ListEval.unary]; omega

section Loop
variable (O : Fin (ns + 1)) (PC : Fin nr) (V : Fin 20 ↪ Fin nr)

/-- One level: `J := J − 1`, its window and power, its record, the window and power cleared. -/
def lvBody : WM ns nr :=
  .seq (.seq (.seq (.seq (.seq (.dec (V 2)) (twW V)) (EwKit.powF (pfE.trans V))) (recE O PC V)) (WM.clear (V 7)))
    (WM.clear (V 8))

/-- The state after `k` levels below the top. -/
def stL (σ : WState ns nr) (w : List Bool) (c t s J k : ℕ) : WState ns nr :=
  (((σ.sets O (w ++ recsDown t s J k)).seth O (w.length + (recsDown t s J k).length)).setv (V 2) (J - k)).setv PC
    (c + (recsDown t s J k).length)

/-- The largest window (level `0`). -/
def twMax (t s : ℕ) : ℕ := 16 * t + 20 * (s + 2)

theorem twOf_le (t s j : ℕ) : twOf t s j ≤ twMax t s := by
  unfold twOf twMax
  have : (s + 1) / 2 ^ (j / 2) ≤ s + 1 := Nat.div_le_self _ _
  omega

/-- A bound on one level's cost. -/
def lvCost (t s J : ℕ) : ℕ :=
  twCost t s J + 1000 * (twMax t s + 1) * (twMax t s + 2) + 40 * (5 * twMax t s + 2) + 3 * (5 * twMax t s + 2) + 200

end Loop

theorem twCost_mono (t s j J : ℕ) (h : j ≤ J) : twCost t s j ≤ twCost t s J := by
  unfold twCost
  have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) h
  have h2 : t + s + j + 2 ^ j + 2 ≤ t + s + J + 2 ^ J + 2 := by omega
  have := Nat.mul_le_mul h2 h2
  nlinarith

theorem recsDown_length_le (t s J k k' : ℕ) (h : k ≤ k') :
    (recsDown t s J k).length ≤ (recsDown t s J k').length := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact le_rfl
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hk | hk
    · rw [recsDown_succ, List.length_append]; have := ih (by omega); omega
    · have : k = k' + 1 := by omega
      subst this; exact le_rfl

section Body
variable (O : Fin (ns + 1)) (PC : Fin nr) (V : Fin 20 ↪ Fin nr)

theorem lvBody_spec (hPC : ∀ i, V i ≠ PC) (σ : WState ns nr) (w : List Bool) (c t s J k : ℕ) (hk : k < J)
    (h0 : σ.val (V 0) = t) (h1 : σ.val (V 1) = s) (hz : ∀ i : Fin 20, 3 ≤ i.val → σ.val (V i) = 0)
    (hw : σ.st O = w) (hh : σ.sh O = w.length)
    (hcap : 2 ^ (J + 1) + J + s + 1000 * (t + s + 2) + 8 * twMax t s + 8 + c + (recsDown t s J J).length +
      5 * twMax t s + 20 ≤ cap) :
    WExec cap (lvBody O PC V) (stL O PC V σ w c t s J k) (stL O PC V σ w c t s J (k + 1)) (lvCost t s J) := by
  have hne : ∀ {i k : Fin 20}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have hV : ∀ i k : Fin 20, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hP' : ∀ i, PC ≠ V i := fun i h => hPC i h.symm
  obtain ⟨j, hj⟩ : ∃ j, j = J - 1 - k := ⟨_, rfl⟩
  obtain ⟨tw, htw⟩ : ∃ tw, tw = twOf t s j := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = 2 ^ Nat.clog 2 (2 * tw + 1) := ⟨_, rfl⟩
  have htm : tw ≤ twMax t s := by rw [htw]; exact twOf_le t s j
  have hpm : p ≤ 2 * (2 * tw + 1) := by rw [hp]; exact EwKit.pow_clog_le2 _ (by omega)
  have hRk : (recsDown t s J k).length ≤ (recsDown t s J J).length := recsDown_length_le t s J k J (by omega)
  have hjJ : j ≤ J := by omega
  have hjp : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hjJ
  have hjp1 : 2 ^ (j + 1) ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 := Nat.one_le_two_pow (n := j + 1)
  have hq2 := Nat.one_le_two_pow (n := J + 1)
  have hq3 := Nat.one_le_two_pow (n := j)
  have hq4 := Nat.one_le_two_pow (n := J)
  have e1 := WExec.dec (cap := cap) (V 2) (stL O PC V σ w c t s J k) (by simp [stL, hV, hPC]; omega)
  obtain ⟨n2, e2, hn2⟩ := twW_spec cap V ((stL O PC V σ w c t s J k).setv (V 2)
      ((stL O PC V σ w c t s J k).val (V 2) - 1)) t s j (by simp [stL, hV, hPC, h0])
    (by simp [stL, hV, hPC, h1]) (by simp [stL, hV, hPC]; omega)
    (fun i hi => by
      have hi2 : i ≠ 2 := by intro e; subst e; simp at hi
      simp [stL, hV, hPC, hi2, hz i hi])
    (by omega)
  rw [← htw] at e2
  obtain ⟨n3, e3, hn3⟩ := EwKit.powF_spec cap (pfE.trans V) ((((stL O PC V σ w c t s J k).setv (V 2)
      ((stL O PC V σ w c t s J k).val (V 2) - 1))).setv (V 7) tw) tw (by simp [hV])
    (by simp [stL, hV, hPC, hz 8 (by decide)]) (by simp [stL, hV, hPC, hz 12 (by decide)])
    (by simp [stL, hV, hPC, hz 13 (by decide)]) (by simp [stL, hV, hPC, hz 14 (by decide)]) (by omega)
  rw [← hp] at e3
  have e4 := recE_spec cap O PC V hPC ((((stL O PC V σ w c t s J k).setv (V 2)
      ((stL O PC V σ w c t s J k).val (V 2) - 1))).setv (V 7) tw |>.setv (V 8) p) (w ++ recsDown t s J k)
      (c + (recsDown t s J k).length) p tw (by simp [stL]) (by simp [stL]) (by simp [stL, hP'])
      (by simp [hV]) (by simp [hV]) (by simp [stL, hV, hPC, hz 10 (by decide)])
      (by simp [stL, hV, hPC, hz 12 (by decide)]) (by omega)
  have c4 := WExec.seq (WExec.seq (WExec.seq e1 e2) e3) e4
  have c5 := WExec.seq c4 (wclear_spec cap (V 7) tw _ (by simp [hV, hPC]) (by simp [hV, hPC]; omega))
  have c6 := WExec.seq c5 (wclear_spec cap (V 8) p _ (by simp [hV, hPC]) (by simp [hV, hPC]; omega))
  refine WExec.cast cap c6 ?_ ?_
  · clear c4 c5 c6 e1 e2 e3 e4
    apply WState.eq
    · funext q
      by_cases hq : q = O
      · subst hq; simp [stL, recsDown_succ, recOf_length, ← hj, ← htw, ← hp]; omega
      · simp [stL, hq]
    · funext q
      by_cases hq : q = O
      · subst hq
        simp [stL, recsDown_succ, recOf, hj, htw, hp]
      · simp [stL, hq]
    · funext q
      by_cases q2 : q = V 2
      · subst q2; simp [stL, hV, hPC]; omega
      · by_cases qP : q = PC
        · subst qP; simp [stL, hP', recsDown_succ, recOf_length, ← hj, ← htw, ← hp]; omega
        · by_cases q7 : q = V 7
          · subst q7; simp [stL, hV, hPC, hz 7 (by decide)]
          · by_cases q8 : q = V 8
            · subst q8; simp [stL, hV, hPC, hz 8 (by decide)]
            · simp [stL, Function.update_apply, q2, qP, q7, q8]
    · simp [stL]
  · have hn2' : n2 ≤ twCost t s J := le_trans hn2 (twCost_mono t s j J hjJ)
    have hn3' : n3 ≤ 1000 * (twMax t s + 1) * (twMax t s + 2) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 1000) (Nat.add_le_add_right htm 1)) (Nat.add_le_add_right htm 2)
      omega
    unfold lvCost
    omega

end Body

end NearCubicWires.WireExponent3_5.UnionMachine.EwLevel
