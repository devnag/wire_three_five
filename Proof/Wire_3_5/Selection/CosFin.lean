import Proof.Wire_3_5.Selection.CosCls4

/-! # C1.5: the coset-selection machine at every input-size degree (P3:1324-1362, 3673)

Paper: "A product-code coset [...] is findable deterministically in `2^{n/2+O(k)}poly(n)` time" (P3:1328-1335, 1359-1360)
for inputs of polynomial size (P3:3071-3072). With the request word at most `(n+1)^d` long, the word width `W` is at most
`16·2^{d+1}·n^{d+1}` (as `n ≥ 8`), and `2^k·2^{s·r/2}·2^{(n+1)/2} ≤ 2·2^{n/2+2k}`. So the machine's cost is within the
selection class of the envelope `selEnv d` (`csel = 2`, `Asel = (d+1)·a`) at the coefficient `selCoef d`
(**`selWithin`**), and **`selImpl`**: the one register machine `Pw`, compiled, implements C1 at every degree
(`c1Impl_of`). Main declarations: `selK`, `selA`, `selEnv`, `selCoef`, **`selWithin`**, **`selImpl`**. Paper quantity:
the selection time `2^{q/2+csel·k}q^{Asel}`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine
open NearCubicWires.WireExponent3_5.Cost (Envelope)
open NearCubicWires.WireExponent3_5.SelectionMachine.Plan (C1Within c1Impl_of BasePre basePre_of)
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (C1Impl)

/-- The coefficient of the machine's uniform cost bound. -/
noncomputable def selK : ℕ := Classical.choose bd_costF

/-- The degree in `W` of the machine's uniform cost bound. -/
noncomputable def selA : ℕ := Classical.choose (Classical.choose_spec bd_costF)

theorem sel_spec (R : SelectionReq) (h : ParamsOk R) : costF parseCostF R ≤ selK * Wof R ^ selA * eK R h :=
  Classical.choose_spec (Classical.choose_spec bd_costF) R h

/-- **C1's envelope at input-size degree `d`**: the selection class `2^{q/2+2k}q^{(d+1)·a}`. -/
noncomputable def selEnv (d : ℕ) : Envelope :=
  { sigma := 0, callDeg := 0, Amain := 0, Atable := 0, Asel := (d + 1) * selA, csel := 2, Apre := 0, cpsi := 0 }

/-- **C1's coefficient at input-size degree `d`.** -/
noncomputable def selCoef (d : ℕ) : ℕ := 2 * selK * (16 * 2 ^ (d + 1)) ^ selA

/-- The word width is polynomial in `n` when the request word is. -/
theorem W_le_poly (R : SelectionReq) (d : ℕ) (hn : 2 ≤ R.n) (hL : Lof R ≤ (R.n + 1) ^ d) :
    Wof R ≤ 16 * (2 ^ (d + 1) * R.n ^ (d + 1)) := by
  have h1 : (R.n + 1) ^ d ≤ 2 ^ d * R.n ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  have h2 : 2 ^ d * R.n ^ d ≤ 2 ^ (d + 1) * R.n ^ (d + 1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : R.n ≤ R.n ^ (d + 1) := Nat.le_self_pow (by omega) _
  have h4 : 2 ≤ 2 ^ (d + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 * R.n ^ (d + 1) ≤ 2 ^ (d + 1) * R.n ^ (d + 1) := Nat.mul_le_mul_right _ h4
  unfold Wof
  omega

/-- All exponentials of the cost within `2·2^{n/2+2k}`. -/
theorem eK_le (R : SelectionReq) (h : ParamsOk R) : eK R h ≤ 2 * 2 ^ (R.n / 2 + 2 * (R.r * R.s)) := by
  have f : R.s * (R.r / 2) ≤ R.r * R.s := by
    rw [Nat.mul_comm R.r]; exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  unfold eK eG e1 eH
  rw [← pow_add, ← pow_add, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The class residual at every degree**: the machine's cost is within C1's selection class. -/
theorem selWithin (d : ℕ) : C1Within d (selEnv d) (selCoef d) (costF parseCostF) := by
  intro R hR
  have hb : BasePre R := basePre_of d _ _ R hR
  have h : ParamsOk R := ⟨hb.1, hb.2.1, hb.2.2.1⟩
  have hL : Lof R ≤ (R.n + 1) ^ d := hR.2
  have hn : 8 ≤ R.n := by have := hb.2.1; have := hb.2.2.1; omega
  have hW := W_le_poly R d (by omega) hL
  have hWa : Wof R ^ selA ≤ (16 * 2 ^ (d + 1)) ^ selA * R.n ^ ((d + 1) * selA) := by
    calc Wof R ^ selA ≤ (16 * (2 ^ (d + 1) * R.n ^ (d + 1))) ^ selA := Nat.pow_le_pow_left hW _
      _ = (16 * 2 ^ (d + 1)) ^ selA * R.n ^ ((d + 1) * selA) := by rw [← Nat.mul_assoc, mul_pow, ← pow_mul]
  have hE := eK_le R h
  show costF parseCostF R ≤ selCoef d * (2 ^ (R.n / 2 + 2 * (R.r * R.s)) * R.n ^ ((d + 1) * selA))
  calc costF parseCostF R ≤ selK * Wof R ^ selA * eK R h := sel_spec R h
    _ ≤ selK * ((16 * 2 ^ (d + 1)) ^ selA * R.n ^ ((d + 1) * selA)) * (2 * 2 ^ (R.n / 2 + 2 * (R.r * R.s))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hWa) hE
    _ = selCoef d * (2 ^ (R.n / 2 + 2 * (R.r * R.s)) * R.n ^ ((d + 1) * selA)) := by unfold selCoef; ring

/-- **The run residual**: the compiled machine runs every admissible request to the selected coset's word. -/
theorem selRun : Plan.C1Run (FinalPass.Tm.WM.toProg Pw).compile (FinalPass.Tm.sTape (nr := 112) (1 : Fin 50))
    (costF parseCostF) :=
  Top.c1Run_of_wm Pw 1 capOf (costF parseCostF) c1WM_Pw

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
