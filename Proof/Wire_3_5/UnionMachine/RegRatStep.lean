import Proof.Wire_3_5.UnionMachine.RegRatMul

/-! # C1.2: the rational accumulation step and the cross-multiplied compare

C1's references (`SelectionMachine.Math`, P3:1324-1362): `RegRat = ℕ × ℕ`,
`ratAccStep (N, D) (a, b, T) = (N·b + a·T·D, D·b)` (add `(a/b)·T`), `ratLt x y = [x.1·y.2 < y.1·x.2]`.
* **`ratStepB Z Q`**: streams `Z = (N, D, a, b, T, T₁, T₂, T₃, S)`, registers `Q = (F, R, G)`:
  `(N, D) := ratAccStep (N, D) (a, b, T)` by five products, a copy and a sum; `a, b, T` kept; scratch back to `0`.
* **`ratLtB Z Q`**: streams `Z = (N₁, D₁, N₂, D₂, T₁, T₂, S)`, registers `Q = (F₀, F, R, G)`:
  `F₀ := [ratLt (N₁, D₁) (N₂, D₂)]`; all words kept; scratch back to `0`.
The stream and register maps are embeddings (pairwise distinct). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.SelectionMachine.Math (ratAccStep ratLt)

variable {ns nr : ℕ}

/-! ## Words under writes -/

theorem numOn_sets_self (σ : WState ns nr) (X : Fin (ns + 1)) (W v : ℕ) (h : σ.sh X = 0) :
    NumOn (σ.sets X (frame (binary W v))) X W v := ⟨by simp, by simp [h]⟩

theorem numOn_sets_other (σ : WState ns nr) (X Y : Fin (ns + 1)) (w : List Bool) (W v : ℕ) (hYX : Y ≠ X)
    (h : NumOn σ Y W v) : NumOn (σ.sets X w) Y W v := ⟨by simp [hYX, h.1], by simp [h.2]⟩

theorem numOn_setv (σ : WState ns nr) (Y : Fin (ns + 1)) (r : Fin nr) (x W v : ℕ) (h : NumOn σ Y W v) :
    NumOn (σ.setv r x) Y W v := ⟨h.1, h.2⟩

/-! ## The step -/

/-- `T₁ := n·b`, `T₂ := a·t`, `T₃ := T₂·d`. -/
def stepProds (Z : Fin 9 ↪ Fin (ns + 1)) (Q : Fin 3 ↪ Fin nr) : WM ns nr :=
  .seq (mulB (Z 0) (Z 3) (Z 5) (Z 8) (Q 0) (Q 1) (Q 2))
  (.seq (mulB (Z 2) (Z 4) (Z 6) (Z 8) (Q 0) (Q 1) (Q 2)) (mulB (Z 6) (Z 1) (Z 7) (Z 8) (Q 0) (Q 1) (Q 2)))

/-- `N := T₁`, `N += T₃`, `T₁ := d·b`, `D := T₁`. -/
def stepSum (Z : Fin 9 ↪ Fin (ns + 1)) (Q : Fin 3 ↪ Fin nr) : WM ns nr :=
  .seq (copyB (Z 0) (Z 5) (Q 0) (Q 1)) (.seq (addB (Z 0) (Z 7) (Q 0) (Q 1))
  (.seq (mulB (Z 1) (Z 3) (Z 5) (Z 8) (Q 0) (Q 1) (Q 2)) (copyB (Z 1) (Z 5) (Q 0) (Q 1))))

/-- Clear `T₁, T₂, T₃`. -/
def stepClear (Z : Fin 9 ↪ Fin (ns + 1)) (Q : Fin 3 ↪ Fin nr) : WM ns nr :=
  .seq (zeroB (Z 5) (Z 2) (Q 0) (Q 1)) (.seq (zeroB (Z 6) (Z 2) (Q 0) (Q 1)) (zeroB (Z 7) (Z 2) (Q 0) (Q 1)))

/-- **`(N, D) := ratAccStep (N, D) (a, b, T)`**. -/
def ratStepB (Z : Fin 9 ↪ Fin (ns + 1)) (Q : Fin 3 ↪ Fin nr) : WM ns nr :=
  .seq (stepProds Z Q) (.seq (stepSum Z Q) (stepClear Z Q))

section Step
variable (cap W : ℕ) (Z : Fin 9 ↪ Fin (ns + 1)) (Q : Fin 3 ↪ Fin nr)

theorem stepProds_spec (σ : WState ns nr) (n d a b t s₁ s₂ s₃ s : ℕ) (hN : NumOn σ (Z 0) W n)
    (hD : NumOn σ (Z 1) W d) (hA : NumOn σ (Z 2) W a) (hB : NumOn σ (Z 3) W b) (hT : NumOn σ (Z 4) W t)
    (h₁ : NumOn σ (Z 5) W s₁) (h₂ : NumOn σ (Z 6) W s₂) (h₃ : NumOn σ (Z 7) W s₃) (hS : NumOn σ (Z 8) W s)
    (hF : σ.val (Q 0) = 0) (hR : σ.val (Q 1) = 0) (hG : σ.val (Q 2) = 0) (hnb : n * b < 2 ^ W)
    (hat : a * t < 2 ^ W) (hatd : a * t * d < 2 ^ W) (hb : b < 2 ^ W) (ht : t < 2 ^ W) (hd : d < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (stepProds Z Q) σ
      ((((((σ.sets (Z 5) (frame (binary W (n * b)))).sets (Z 8) (frame (binary W 0))).sets (Z 6)
        (frame (binary W (a * t)))).sets (Z 8) (frame (binary W 0))).sets (Z 7) (frame (binary W (a * t * d)))).sets
        (Z 8) (frame (binary W 0))) (3 * mulCost W + 2) := by
  have z : ∀ i j : Fin 9, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have q : ∀ i j : Fin 3, i ≠ j → Q i ≠ Q j := fun i j h => Q.injective.ne h
  have s1 := mulB_spec cap W (z 0 3 (by decide)) (z 0 5 (by decide)) (z 0 8 (by decide)) (z 3 5 (by decide))
    (z 3 8 (by decide)) (z 5 8 (by decide)) (q 0 1 (by decide)) (q 0 2 (by decide)) (q 1 2 (by decide))
    σ n b s₁ s hN hB h₁ hS hF hR hG hnb hb hcap
  set σ1 := (σ.sets (Z 5) (frame (binary W (n * b)))).sets (Z 8) (frame (binary W 0)) with hσ1
  have o1 : ∀ (Y : Fin 9) (v : ℕ), Y ≠ 5 → Y ≠ 8 → NumOn σ (Z Y) W v → NumOn σ1 (Z Y) W v := fun Y v h5 h8 h =>
    numOn_sets_other _ _ _ _ _ _ (z Y 8 h8) (numOn_sets_other _ _ _ _ _ _ (z Y 5 h5) h)
  have s2 := mulB_spec cap W (z 2 4 (by decide)) (z 2 6 (by decide)) (z 2 8 (by decide)) (z 4 6 (by decide))
    (z 4 8 (by decide)) (z 6 8 (by decide)) (q 0 1 (by decide)) (q 0 2 (by decide)) (q 1 2 (by decide))
    σ1 a t s₂ 0 (o1 2 a (by decide) (by decide) hA) (o1 4 t (by decide) (by decide) hT)
    (o1 6 s₂ (by decide) (by decide) h₂) (numOn_sets_self _ _ _ _ (by simp [hS.2])) (by simp [hσ1, hF])
    (by simp [hσ1, hR]) (by simp [hσ1, hG]) hat ht hcap
  set σ2 := (σ1.sets (Z 6) (frame (binary W (a * t)))).sets (Z 8) (frame (binary W 0)) with hσ2
  have o2 : ∀ (Y : Fin 9) (v : ℕ), Y ≠ 6 → Y ≠ 8 → NumOn σ1 (Z Y) W v → NumOn σ2 (Z Y) W v := fun Y v h6 h8 h =>
    numOn_sets_other _ _ _ _ _ _ (z Y 8 h8) (numOn_sets_other _ _ _ _ _ _ (z Y 6 h6) h)
  have T2 : NumOn σ2 (Z 6) W (a * t) := numOn_sets_other _ _ _ _ _ _ (z 6 8 (by decide))
    (numOn_sets_self _ _ _ _ (o1 6 s₂ (by decide) (by decide) h₂).2)
  have s3 := mulB_spec cap W (z 6 1 (by decide)) (z 6 7 (by decide)) (z 6 8 (by decide)) (z 1 7 (by decide))
    (z 1 8 (by decide)) (z 7 8 (by decide)) (q 0 1 (by decide)) (q 0 2 (by decide)) (q 1 2 (by decide))
    σ2 (a * t) d s₃ 0 T2 (o2 1 d (by decide) (by decide) (o1 1 d (by decide) (by decide) hD))
    (o2 7 s₃ (by decide) (by decide) (o1 7 s₃ (by decide) (by decide) h₃))
    (numOn_sets_self _ _ _ _ (by simp [hσ1, hS.2])) (by simp [hσ2, hσ1, hF]) (by simp [hσ2, hσ1, hR])
    (by simp [hσ2, hσ1, hG]) hatd hd hcap
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

theorem stepSum_spec (τ : WState ns nr) (n d b u v : ℕ) (hN : NumOn τ (Z 0) W n) (hD : NumOn τ (Z 1) W d)
    (hB : NumOn τ (Z 3) W b) (h₁ : NumOn τ (Z 5) W u) (h₃ : NumOn τ (Z 7) W v) (hS : NumOn τ (Z 8) W 0)
    (hF : τ.val (Q 0) = 0) (hR : τ.val (Q 1) = 0) (hG : τ.val (Q 2) = 0) (huv : u + v < 2 ^ W)
    (hdb : d * b < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (stepSum Z Q) τ
      (((((τ.sets (Z 0) (frame (binary W u))).sets (Z 0) (frame (binary W (u + v)))).sets (Z 5)
        (frame (binary W (d * b)))).sets (Z 8) (frame (binary W 0))).sets (Z 1) (frame (binary W (d * b))))
      (mulCost W + 3 * (41 * W + 3) + 3) := by
  have z : ∀ i j : Fin 9, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have q : ∀ i j : Fin 3, i ≠ j → Q i ≠ Q j := fun i j h => Q.injective.ne h
  have s4 := copyB_spec cap W (z 0 5 (by decide)) (q 0 1 (by decide)) τ n u hN h₁ hF hR hcap
  set τ4 := τ.sets (Z 0) (frame (binary W u)) with hτ4
  have s5 := addB_spec cap W (z 0 7 (by decide)) (q 0 1 (by decide)) τ4 u v (numOn_sets_self _ _ _ _ hN.2)
    (numOn_sets_other _ _ _ _ _ _ (z 7 0 (by decide)) h₃) (by simp [hτ4, hF]) (by simp [hτ4, hR]) huv hcap
  set τ5 := τ4.sets (Z 0) (frame (binary W (u + v))) with hτ5
  have o5 : ∀ (Y : Fin 9) (w : ℕ), Y ≠ 0 → NumOn τ (Z Y) W w → NumOn τ5 (Z Y) W w := fun Y w h0 h =>
    numOn_sets_other _ _ _ _ _ _ (z Y 0 h0) (numOn_sets_other _ _ _ _ _ _ (z Y 0 h0) h)
  have s6 := mulB_spec cap W (z 1 3 (by decide)) (z 1 5 (by decide)) (z 1 8 (by decide)) (z 3 5 (by decide))
    (z 3 8 (by decide)) (z 5 8 (by decide)) (q 0 1 (by decide)) (q 0 2 (by decide)) (q 1 2 (by decide))
    τ5 d b u 0 (o5 1 d (by decide) hD) (o5 3 b (by decide) hB) (o5 5 u (by decide) h₁) (o5 8 0 (by decide) hS)
    (by simp [hτ5, hτ4, hF]) (by simp [hτ5, hτ4, hR]) (by simp [hτ5, hτ4, hG]) hdb hb hcap
  set τ6 := (τ5.sets (Z 5) (frame (binary W (d * b)))).sets (Z 8) (frame (binary W 0)) with hτ6
  have s7 := copyB_spec cap W (z 1 5 (by decide)) (q 0 1 (by decide)) τ6 d (d * b)
    (numOn_sets_other _ _ _ _ _ _ (z 1 8 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 1 5 (by decide))
      (o5 1 d (by decide) hD)))
    (numOn_sets_other _ _ _ _ _ _ (z 5 8 (by decide)) (numOn_sets_self _ _ _ _ (o5 5 u (by decide) h₁).2))
    (by simp [hτ6, hτ5, hτ4, hF]) (by simp [hτ6, hτ5, hτ4, hR]) hcap
  exact WExec.mono (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))) (by omega)

theorem stepClear_spec (ρ : WState ns nr) (a v₁ v₂ v₃ : ℕ) (hA : NumOn ρ (Z 2) W a) (h₁ : NumOn ρ (Z 5) W v₁)
    (h₂ : NumOn ρ (Z 6) W v₂) (h₃ : NumOn ρ (Z 7) W v₃) (hF : ρ.val (Q 0) = 0) (hR : ρ.val (Q 1) = 0)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (stepClear Z Q) ρ (((ρ.sets (Z 5) (frame (binary W 0))).sets (Z 6) (frame (binary W 0))).sets (Z 7)
      (frame (binary W 0))) (3 * (41 * W + 3) + 2) := by
  have z : ∀ i j : Fin 9, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have q : ∀ i j : Fin 3, i ≠ j → Q i ≠ Q j := fun i j h => Q.injective.ne h
  have s8 := zeroB_spec cap W (z 5 2 (by decide)) (q 0 1 (by decide)) ρ v₁ a h₁ hA hF hR hcap
  have s9 := zeroB_spec cap W (z 6 2 (by decide)) (q 0 1 (by decide)) (ρ.sets (Z 5) (frame (binary W 0))) v₂ a
    (numOn_sets_other _ _ _ _ _ _ (z 6 5 (by decide)) h₂) (numOn_sets_other _ _ _ _ _ _ (z 2 5 (by decide)) hA)
    (by simp [hF]) (by simp [hR]) hcap
  have s10 := zeroB_spec cap W (z 7 2 (by decide)) (q 0 1 (by decide))
    ((ρ.sets (Z 5) (frame (binary W 0))).sets (Z 6) (frame (binary W 0))) v₃ a
    (numOn_sets_other _ _ _ _ _ _ (z 7 6 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 7 5 (by decide)) h₃))
    (numOn_sets_other _ _ _ _ _ _ (z 2 6 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 2 5 (by decide)) hA))
    (by simp [hF]) (by simp [hR]) hcap
  exact WExec.mono (WExec.seq s8 (WExec.seq s9 s10)) (by omega)

/-- The writes of the step, collapsed. -/
theorem ratStep_eq (σ : WState ns nr) (u v w x y : List Bool) (e : List Bool) :
    ((((((((((((((σ.sets (Z 5) u).sets (Z 8) e).sets (Z 6) v).sets (Z 8) e).sets (Z 7) w).sets (Z 8) e).sets (Z 0)
      u).sets (Z 0) x).sets (Z 5) y).sets (Z 8) e).sets (Z 1) y).sets (Z 5) e).sets (Z 6) e).sets (Z 7) e) =
    (((((σ.sets (Z 0) x).sets (Z 1) y).sets (Z 5) e).sets (Z 6) e).sets (Z 7) e).sets (Z 8) e := by
  have z : ∀ i j : Fin 9, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have z01 := z 0 1 (by decide); have z05 := z 0 5 (by decide); have z06 := z 0 6 (by decide)
  have z07 := z 0 7 (by decide); have z08 := z 0 8 (by decide); have z15 := z 1 5 (by decide)
  have z16 := z 1 6 (by decide); have z17 := z 1 7 (by decide); have z18 := z 1 8 (by decide)
  have z56 := z 5 6 (by decide); have z57 := z 5 7 (by decide); have z58 := z 5 8 (by decide)
  have z67 := z 6 7 (by decide); have z68 := z 6 8 (by decide); have z78 := z 7 8 (by decide)
  apply WState.eq
  · simp
  · funext i
    simp only [WState.sets_st]
    by_cases e0 : i = Z 0
    · rw [e0]; simp only [Function.update_apply, z01, z05, z06, z07, z08, if_false, if_true]
    · by_cases e1 : i = Z 1
      · rw [e1]; simp only [Function.update_apply, Ne.symm z01, z15, z16, z17, z18, if_false, if_true]
      · by_cases e5 : i = Z 5
        · rw [e5]; simp only [Function.update_apply, Ne.symm z05, Ne.symm z15, z56, z57, z58, if_false, if_true]
        · by_cases e6 : i = Z 6
          · rw [e6]
            simp only [Function.update_apply, Ne.symm z06, Ne.symm z16, Ne.symm z56, z67, z68, if_false, if_true]
          · by_cases e7 : i = Z 7
            · rw [e7]
              simp only [Function.update_apply, Ne.symm z07, Ne.symm z17, Ne.symm z57, Ne.symm z67, z78, if_false,
                if_true]
            · by_cases e8 : i = Z 8
              · rw [e8]
                simp only [Function.update_apply, Ne.symm z08, Ne.symm z18, Ne.symm z58, Ne.symm z68, Ne.symm z78,
                  if_false, if_true]
              · simp only [Function.update_apply, e0, e1, e5, e6, e7, e8, if_false]
  · simp
  · simp

/-- The step's cost. -/
def ratStepCost (W : ℕ) : ℕ := 4 * mulCost W + 6 * (41 * W + 3) + 9

theorem ratStepB_spec (σ : WState ns nr) (n d a b t s₁ s₂ s₃ s : ℕ) (hN : NumOn σ (Z 0) W n)
    (hD : NumOn σ (Z 1) W d) (hA : NumOn σ (Z 2) W a) (hB : NumOn σ (Z 3) W b) (hT : NumOn σ (Z 4) W t)
    (h₁ : NumOn σ (Z 5) W s₁) (h₂ : NumOn σ (Z 6) W s₂) (h₃ : NumOn σ (Z 7) W s₃) (hS : NumOn σ (Z 8) W s)
    (hF : σ.val (Q 0) = 0) (hR : σ.val (Q 1) = 0) (hG : σ.val (Q 2) = 0) (hd1 : 1 ≤ d)
    (hsum : n * b + a * t * d < 2 ^ W) (hdb : d * b < 2 ^ W) (hb : b < 2 ^ W) (ht : t < 2 ^ W) (hd : d < 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (ratStepB Z Q) σ
      ((((((σ.sets (Z 0) (frame (binary W (ratAccStep (n, d) (a, b, t)).1))).sets (Z 1)
        (frame (binary W (ratAccStep (n, d) (a, b, t)).2))).sets (Z 5) (frame (binary W 0))).sets (Z 6)
        (frame (binary W 0))).sets (Z 7) (frame (binary W 0))).sets (Z 8) (frame (binary W 0)))
      (ratStepCost W) := by
  have z : ∀ i j : Fin 9, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have hat : a * t ≤ a * t * d := Nat.le_mul_of_pos_right _ hd1
  have pA := stepProds_spec cap W Z Q σ n d a b t s₁ s₂ s₃ s hN hD hA hB hT h₁ h₂ h₃ hS hF hR hG (by omega)
    (by omega) (by omega) hb ht hd hcap
  set σA := (((((σ.sets (Z 5) (frame (binary W (n * b)))).sets (Z 8) (frame (binary W 0))).sets (Z 6)
    (frame (binary W (a * t)))).sets (Z 8) (frame (binary W 0))).sets (Z 7) (frame (binary W (a * t * d)))).sets
    (Z 8) (frame (binary W 0)) with hσA
  have oA : ∀ (Y : Fin 9) (v : ℕ), Y ≠ 5 → Y ≠ 6 → Y ≠ 7 → Y ≠ 8 → NumOn σ (Z Y) W v → NumOn σA (Z Y) W v :=
    fun Y v h5 h6 h7 h8 h => numOn_sets_other _ _ _ _ _ _ (z Y 8 h8) (numOn_sets_other _ _ _ _ _ _ (z Y 7 h7)
      (numOn_sets_other _ _ _ _ _ _ (z Y 8 h8) (numOn_sets_other _ _ _ _ _ _ (z Y 6 h6)
        (numOn_sets_other _ _ _ _ _ _ (z Y 8 h8) (numOn_sets_other _ _ _ _ _ _ (z Y 5 h5) h)))))
  have A5 : NumOn σA (Z 5) W (n * b) := numOn_sets_other _ _ _ _ _ _ (z 5 8 (by decide))
    (numOn_sets_other _ _ _ _ _ _ (z 5 7 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 5 8 (by decide))
      (numOn_sets_other _ _ _ _ _ _ (z 5 6 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 5 8 (by decide))
        (numOn_sets_self _ _ _ _ h₁.2)))))
  have A6 : NumOn σA (Z 6) W (a * t) := numOn_sets_other _ _ _ _ _ _ (z 6 8 (by decide))
    (numOn_sets_other _ _ _ _ _ _ (z 6 7 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 6 8 (by decide))
      (numOn_sets_self _ _ _ _ (by simp [h₂.2]))))
  have A7 : NumOn σA (Z 7) W (a * t * d) := numOn_sets_other _ _ _ _ _ _ (z 7 8 (by decide))
    (numOn_sets_self _ _ _ _ (by simp [h₃.2]))
  have A8 : NumOn σA (Z 8) W 0 := numOn_sets_self _ _ _ _ (by simp [hS.2])
  have pB := stepSum_spec cap W Z Q σA n d b (n * b) (a * t * d) (oA 0 n (by decide) (by decide) (by decide)
    (by decide) hN) (oA 1 d (by decide) (by decide) (by decide) (by decide) hD)
    (oA 3 b (by decide) (by decide) (by decide) (by decide) hB) A5 A7 A8 (by simp [hσA, hF]) (by simp [hσA, hR])
    (by simp [hσA, hG]) hsum hdb hb hcap
  set σB := ((((σA.sets (Z 0) (frame (binary W (n * b)))).sets (Z 0) (frame (binary W (n * b + a * t * d)))).sets
    (Z 5) (frame (binary W (d * b)))).sets (Z 8) (frame (binary W 0))).sets (Z 1) (frame (binary W (d * b)))
    with hσB
  have oB : ∀ (Y : Fin 9) (v : ℕ), Y ≠ 0 → Y ≠ 1 → Y ≠ 5 → Y ≠ 8 → NumOn σA (Z Y) W v → NumOn σB (Z Y) W v :=
    fun Y v h0 h1 h5 h8 h => numOn_sets_other _ _ _ _ _ _ (z Y 1 h1) (numOn_sets_other _ _ _ _ _ _ (z Y 8 h8)
      (numOn_sets_other _ _ _ _ _ _ (z Y 5 h5) (numOn_sets_other _ _ _ _ _ _ (z Y 0 h0)
        (numOn_sets_other _ _ _ _ _ _ (z Y 0 h0) h))))
  have B5 : NumOn σB (Z 5) W (d * b) := numOn_sets_other _ _ _ _ _ _ (z 5 1 (by decide))
    (numOn_sets_other _ _ _ _ _ _ (z 5 8 (by decide)) (numOn_sets_self _ _ _ _ A5.2))
  have pC := stepClear_spec cap W Z Q σB a (d * b) (a * t) (a * t * d)
    (oB 2 a (by decide) (by decide) (by decide) (by decide) (oA 2 a (by decide) (by decide) (by decide)
      (by decide) hA)) B5 (oB 6 _ (by decide) (by decide) (by decide) (by decide) A6)
    (oB 7 _ (by decide) (by decide) (by decide) (by decide) A7) (by simp [hσB, hσA, hF]) (by simp [hσB, hσA, hR])
    hcap
  refine WExec.cast cap (WExec.seq pA (WExec.seq pB pC)) ?_ (by unfold ratStepCost; omega)
  simp only [hσB, hσA, ratAccStep]
  exact ratStep_eq Z σ _ _ _ _ _ _

end Step

/-! ## The compare -/

/-- **`F₀ := [ratLt (N₁, D₁) (N₂, D₂)]`**: `T₁ := n₁·d₂`, `T₂ := n₂·d₁`, `F₀ := [T₁ < T₂]`, clear `T₁, T₂`. -/
def ratLtB (Z : Fin 7 ↪ Fin (ns + 1)) (Q : Fin 4 ↪ Fin nr) : WM ns nr :=
  .seq (mulB (Z 0) (Z 3) (Z 4) (Z 6) (Q 1) (Q 2) (Q 3)) (.seq (mulB (Z 2) (Z 1) (Z 5) (Z 6) (Q 1) (Q 2) (Q 3))
    (.seq (ltB (Z 4) (Z 5) (Q 0) (Q 2)) (.seq (zeroB (Z 4) (Z 0) (Q 1) (Q 2)) (zeroB (Z 5) (Z 0) (Q 1) (Q 2)))))

section Lt
variable (cap W : ℕ) (Z : Fin 7 ↪ Fin (ns + 1)) (Q : Fin 4 ↪ Fin nr)

/-- The writes of the compare, collapsed. -/
theorem ratLt_eq (σ : WState ns nr) (u v e : List Bool) (r : ℕ) :
    ((((((σ.sets (Z 4) u).sets (Z 6) e).sets (Z 5) v).sets (Z 6) e).setv (Q 0) r).sets (Z 4) e).sets (Z 5) e =
    (((σ.sets (Z 4) e).sets (Z 5) e).sets (Z 6) e).setv (Q 0) r := by
  have z : ∀ i j : Fin 7, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have z45 := z 4 5 (by decide); have z46 := z 4 6 (by decide); have z56 := z 5 6 (by decide)
  apply WState.eq
  · simp
  · funext i
    simp only [WState.sets_st, WState.setv_st]
    by_cases e4 : i = Z 4
    · rw [e4]; simp only [Function.update_apply, z45, z46, if_false, if_true]
    · by_cases e5 : i = Z 5
      · rw [e5]; simp only [Function.update_apply, Ne.symm z45, z56, if_false, if_true]
      · by_cases e6 : i = Z 6
        · rw [e6]; simp only [Function.update_apply, Ne.symm z46, Ne.symm z56, if_false, if_true]
        · simp only [Function.update_apply, e4, e5, e6, if_false]
  · simp
  · simp

/-- The compare's cost. -/
def ratLtCost (W : ℕ) : ℕ := 2 * mulCost W + 3 * (41 * W + 3) + 4

theorem ratLtB_spec (σ : WState ns nr) (n₁ d₁ n₂ d₂ s₁ s₂ s : ℕ) (hN₁ : NumOn σ (Z 0) W n₁)
    (hD₁ : NumOn σ (Z 1) W d₁) (hN₂ : NumOn σ (Z 2) W n₂) (hD₂ : NumOn σ (Z 3) W d₂) (h₁ : NumOn σ (Z 4) W s₁)
    (h₂ : NumOn σ (Z 5) W s₂) (hS : NumOn σ (Z 6) W s) (hF₀ : σ.val (Q 0) = 0) (hF : σ.val (Q 1) = 0)
    (hR : σ.val (Q 2) = 0) (hG : σ.val (Q 3) = 0) (h12 : n₁ * d₂ < 2 ^ W) (h21 : n₂ * d₁ < 2 ^ W)
    (hd₁ : d₁ < 2 ^ W) (hd₂ : d₂ < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (ratLtB Z Q) σ ((((σ.sets (Z 4) (frame (binary W 0))).sets (Z 5) (frame (binary W 0))).sets (Z 6)
      (frame (binary W 0))).setv (Q 0) (ratLt (n₁, d₁) (n₂, d₂)).toNat) (ratLtCost W) := by
  have z : ∀ i j : Fin 7, i ≠ j → Z i ≠ Z j := fun i j h => Z.injective.ne h
  have q : ∀ i j : Fin 4, i ≠ j → Q i ≠ Q j := fun i j h => Q.injective.ne h
  have s1 := mulB_spec cap W (z 0 3 (by decide)) (z 0 4 (by decide)) (z 0 6 (by decide)) (z 3 4 (by decide))
    (z 3 6 (by decide)) (z 4 6 (by decide)) (q 1 2 (by decide)) (q 1 3 (by decide)) (q 2 3 (by decide))
    σ n₁ d₂ s₁ s hN₁ hD₂ h₁ hS hF hR hG h12 hd₂ hcap
  set σ1 := (σ.sets (Z 4) (frame (binary W (n₁ * d₂)))).sets (Z 6) (frame (binary W 0)) with hσ1
  have o1 : ∀ (Y : Fin 7) (v : ℕ), Y ≠ 4 → Y ≠ 6 → NumOn σ (Z Y) W v → NumOn σ1 (Z Y) W v := fun Y v h4 h6 h =>
    numOn_sets_other _ _ _ _ _ _ (z Y 6 h6) (numOn_sets_other _ _ _ _ _ _ (z Y 4 h4) h)
  have s2 := mulB_spec cap W (z 2 1 (by decide)) (z 2 5 (by decide)) (z 2 6 (by decide)) (z 1 5 (by decide))
    (z 1 6 (by decide)) (z 5 6 (by decide)) (q 1 2 (by decide)) (q 1 3 (by decide)) (q 2 3 (by decide))
    σ1 n₂ d₁ s₂ 0 (o1 2 n₂ (by decide) (by decide) hN₂) (o1 1 d₁ (by decide) (by decide) hD₁)
    (o1 5 s₂ (by decide) (by decide) h₂) (numOn_sets_self _ _ _ _ (by simp [hS.2])) (by simp [hσ1, hF])
    (by simp [hσ1, hR]) (by simp [hσ1, hG]) h21 hd₁ hcap
  set σ2 := (σ1.sets (Z 5) (frame (binary W (n₂ * d₁)))).sets (Z 6) (frame (binary W 0)) with hσ2
  have T1 : NumOn σ2 (Z 4) W (n₁ * d₂) := numOn_sets_other _ _ _ _ _ _ (z 4 6 (by decide))
    (numOn_sets_other _ _ _ _ _ _ (z 4 5 (by decide)) (numOn_sets_other _ _ _ _ _ _ (z 4 6 (by decide))
      (numOn_sets_self _ _ _ _ h₁.2)))
  have T2 : NumOn σ2 (Z 5) W (n₂ * d₁) := numOn_sets_other _ _ _ _ _ _ (z 5 6 (by decide))
    (numOn_sets_self _ _ _ _ (o1 5 s₂ (by decide) (by decide) h₂).2)
  have s3 := ltB_spec cap W (z 4 5 (by decide)) (q 0 2 (by decide)) σ2 (n₁ * d₂) (n₂ * d₁) T1 T2
    (by simp [hσ2, hσ1, hF₀]) (by simp [hσ2, hσ1, hR]) h12 h21 hcap
  set σ3 := σ2.setv (Q 0) (decide (n₁ * d₂ < n₂ * d₁)).toNat with hσ3
  have N3 : NumOn σ3 (Z 0) W n₁ := numOn_setv _ _ _ _ _ _ (numOn_sets_other _ _ _ _ _ _ (z 0 6 (by decide))
    (numOn_sets_other _ _ _ _ _ _ (z 0 5 (by decide)) (o1 0 n₁ (by decide) (by decide) hN₁)))
  have s4 := zeroB_spec cap W (z 4 0 (by decide)) (q 1 2 (by decide)) σ3 (n₁ * d₂) n₁
    (numOn_setv _ _ _ _ _ _ T1) N3 (by simp [hσ3, hσ2, hσ1, q 1 0 (by decide), hF])
    (by simp [hσ3, hσ2, hσ1, q 2 0 (by decide), hR]) hcap
  have s5 := zeroB_spec cap W (z 5 0 (by decide)) (q 1 2 (by decide)) (σ3.sets (Z 4) (frame (binary W 0)))
    (n₂ * d₁) n₁ (numOn_sets_other _ _ _ _ _ _ (z 5 4 (by decide)) (numOn_setv _ _ _ _ _ _ T2))
    (numOn_sets_other _ _ _ _ _ _ (z 0 4 (by decide)) N3) (by simp [hσ3, hσ2, hσ1, q 1 0 (by decide), hF])
    (by simp [hσ3, hσ2, hσ1, q 2 0 (by decide), hR]) hcap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_
    (by unfold ratLtCost; omega)
  simp only [hσ3, hσ2, hσ1]
  exact ratLt_eq Z Q σ _ _ _ _

end Lt

end NearCubicWires.WireExponent3_5.UnionMachine.RegRat
