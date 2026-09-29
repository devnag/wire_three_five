import Proof.Wire_3_5.FinalPass.SymF7
import Proof.Wire_3_5.FinalPass.TabBd2

/-! # SWf (the SYM words writer's flat tables), part 8: the writer's size hypotheses

At the flat list's numbers `M, B, errExp`, the population length `L` and the seed count `|FlatSeed|`, all at most
`X = K₀·Q^{E₀}` at the writer's dimension `Q = 2^m + 1` (`n + 2 ≤ Q`): the cell capacity `capP = A₁·Q^{3E₀}` (PA's
setup `runNeed`, the builder's `hcapC`, `hO`, the table's length, the request, the loop bound), the per-unit cost
`A₂·Q^{9E₀}` (the decode, PA's setup `popCost` at `capP`, the table stages, the emission), the scrub capacity
`CWP·Q^{9E₀}` above both and the boot, the loop bound `K₀·Q^{E₀}` past `|FlatSeed|`. **`tabP_hyps`**: every size
hypothesis of `tabP_writer` but its budget.

Paper quantity of the main type: the flat tables writer's time and space, polynomial in the dimension `2^m`
(list:flatten P3:1505-1520; prim:runtime P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.BlockPlatform NearCubicWires.SupplierPipeline

/-- The cell capacity's coefficient. -/
def A1P (K0 : ℕ) : ℕ := 100000000 * K0 ^ 3 + 1000

/-- The per-unit cost's coefficient. -/
def A2P (K0 : ℕ) : ℕ :=
  1000000 * (A1P K0 + 1) ^ 3 + 100000000 * 70 ^ 5 * K0 ^ 5 + 300 * (A1P K0 + 1) ^ 2 + 1000000 * K0 ^ 3 +
    10000 * K0 + 10000

/-- The scrub's coefficient. -/
def CWP (K0 : ℕ) : ℕ := A1P K0 + A2P K0 + 4000 * K0 + 2000

/-- **The flat tables writer's size hypotheses** at the flat list's numbers `≤ K₀·Q^{E₀}`. -/
theorem tabP_hyps (m : ℕ) (Pl : FlatListParams) (n L K0 E0 : ℕ) (hQ : n + 2 ≤ 2 ^ m + 1) (hK0 : 1 ≤ K0)
    (hE0 : 1 ≤ E0) (hM : Pl.M ≤ K0 * (2 ^ m + 1) ^ E0) (hB : Pl.B ≤ K0 * (2 ^ m + 1) ^ E0)
    (hE : Pl.errExp ≤ K0 * (2 ^ m + 1) ^ E0) (hL : L ≤ K0 * (2 ^ m + 1) ^ E0)
    (hK : Fintype.card Pl.FlatSeed ≤ K0 * (2 ^ m + 1) ^ E0) :
    Fintype.card Pl.FlatSeed ≤ UnaryCalc.value E0 K0 (2 ^ m) ∧
    A1P K0 * (2 ^ m + 1) ^ (3 * E0) + 1 ≤ UnaryCalc.value (9 * E0) (CWP K0) (2 ^ m) ∧
    A2P K0 * (2 ^ m + 1) ^ (9 * E0) + 1 ≤ UnaryCalc.value (9 * E0) (CWP K0) (2 ^ m) ∧
    ShellD.bootCost (reqP n Pl L) n 0 0 ≤ UnaryCalc.value (9 * E0) (CWP K0) (2 ^ m) ∧
    (∀ f off, f ≤ Fintype.card Pl.FlatSeed → off ≤ Fintype.card Pl.FlatSeed →
      PopSetupRun.runNeed Pl.M Pl.B Pl.errExp f 0 0 0 0 off L ≤ A1P K0 * (2 ^ m + 1) ^ (3 * E0)) ∧
    8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ A1P K0 * (2 ^ m + 1) ^ (3 * E0) ∧
    (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < A1P K0 * (2 ^ m + 1) ^ (3 * E0) ∧
    tabLenP Pl L ≤ A1P K0 * (2 ^ m + 1) ^ (3 * E0) ∧
    2 * (reqP n Pl L).length + 2 ≤ A1P K0 * (2 ^ m + 1) ^ (3 * E0) ∧
    UnaryCalc.value E0 K0 (2 ^ m) ≤ A1P K0 * (2 ^ m + 1) ^ (3 * E0) ∧
    (∀ j < UnaryCalc.value E0 K0 (2 ^ m),
      cpCost (Data.unaryList [0]).length + 1 + (decBoundP (reqP n Pl L).length j + 1 +
        PopSetupRun.popCost (A1P K0 * (2 ^ m + 1) ^ (3 * E0)) + 1 + tabPrePCost Pl L (PopSetup.popRW Pl)
          (PopSetup.popRW Pl) + 1 + emitPBound (A1P K0 * (2 ^ m + 1) ^ (3 * E0)) j (tabLenP Pl L)) ≤
        A2P K0 * (2 ^ m + 1) ^ (9 * E0)) := by
  have ev : ∀ D C, UnaryCalc.value D C (2 ^ m) = C * (2 ^ m + 1) ^ D := fun D C => rfl
  simp only [ev]
  obtain ⟨Q, hQd⟩ : ∃ q, q = 2 ^ m + 1 := ⟨_, rfl⟩
  rw [← hQd] at hQ hM hB hE hL hK ⊢
  have hQ1 : 1 ≤ Q := by omega
  obtain ⟨y0, hy0⟩ : ∃ y, y = Q ^ E0 := ⟨_, rfl⟩
  have hy1e : Q ^ (3 * E0) = y0 ^ 3 := by rw [hy0, ← pow_mul, Nat.mul_comm]
  have hy2e : Q ^ (9 * E0) = y0 ^ 9 := by rw [hy0, ← pow_mul, Nat.mul_comm]
  rw [← hy0] at hM hB hE hL hK ⊢
  rw [hy1e, hy2e]
  have hy01 : 1 ≤ y0 := by rw [hy0]; exact Nat.one_le_pow _ _ hQ1
  have hQy : Q ≤ y0 := by
    rw [hy0]
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ E0 := Nat.pow_le_pow_right hQ1 hE0
  -- the atom `X = K₀·y₀`
  obtain ⟨X, hXd⟩ : ∃ x, x = K0 * y0 := ⟨_, rfl⟩
  rw [← hXd] at hM hB hE hL hK
  have hy0X : y0 ≤ X := by rw [hXd]; exact Nat.le_mul_of_pos_left y0 hK0
  have hX1 : 1 ≤ X := by omega
  have hnX : n + 2 ≤ X := by omega
  have hK3 : K0 ≤ K0 ^ 3 := Nat.le_self_pow (by norm_num) K0
  -- powers of `y₀` and `X`
  have p3 : y0 ≤ y0 ^ 3 := Nat.le_self_pow (by norm_num) y0
  have p9 : y0 ^ 3 ≤ y0 ^ 9 := Nat.pow_le_pow_right hy01 (by norm_num)
  have p59 : y0 ^ 5 ≤ y0 ^ 9 := Nat.pow_le_pow_right hy01 (by norm_num)
  have p69 : y0 ^ 6 ≤ y0 ^ 9 := Nat.pow_le_pow_right hy01 (by norm_num)
  have x2 : X * X ≤ K0 ^ 3 * y0 ^ 3 := by
    rw [hXd]
    have : K0 * y0 * (K0 * y0) = K0 ^ 2 * y0 ^ 2 := by ring
    rw [this]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right hK0 (by norm_num)) (Nat.pow_le_pow_right hy01 (by norm_num))
  have x3 : (X + 1) * (X + 1) * (X + 1) ≤ 8 * (K0 ^ 3 * y0 ^ 3) := by
    have h : (X + 1) * (X + 1) * (X + 1) ≤ (2 * X) * (2 * X) * (2 * X) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    have e : (2 * X) * (2 * X) * (2 * X) = 8 * (K0 ^ 3 * y0 ^ 3) := by rw [hXd]; ring
    omega
  have x5 : (10 * X + 60) ^ 5 ≤ 70 ^ 5 * (K0 ^ 5 * y0 ^ 5) := by
    have h : (10 * X + 60) ^ 5 ≤ (70 * X) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    have e : (70 * X) ^ 5 = 70 ^ 5 * (K0 ^ 5 * y0 ^ 5) := by rw [hXd]; ring
    omega
  -- the pieces at `X`
  obtain ⟨sy, sN, sC, sO, sT⟩ := sizes_le Pl L 0 0 X hX1 hM hB hE hL (by omega) (by omega)
  have sN' : ∀ f off, f ≤ Fintype.card Pl.FlatSeed → off ≤ Fintype.card Pl.FlatSeed →
      PopSetupRun.runNeed Pl.M Pl.B Pl.errExp f 0 0 0 0 off L ≤ 40000000 * (X * X) := fun f off hf ho =>
    (sizes_le Pl L f off X hX1 hM hB hE hL (by omega) (by omega)).2.1
  have hw := TabW.reqT_le n Pl.M Pl.B Pl.errExp L 0 (Fintype.card Pl.FlatSeed) X hnX hM hB hE hL (by omega) hK
  have hw' : (reqP n Pl L).length ≤ 16 * X := hw
  have hboot := TabW.boot_le (reqP n Pl L) n (16 * X) hw' (by omega)
  have htp : tabPrePCost Pl L (PopSetup.popRW Pl) (PopSetup.popRW Pl) ≤
      100000000 * 70 ^ 5 * K0 ^ 5 * y0 ^ 9 := by
    have h1 := tabPre_le Pl L
    have h2 : (yOf Pl L) ^ 5 ≤ (10 * X + 60) ^ 5 := Nat.pow_le_pow_left sy 5
    have h3 : 70 ^ 5 * (K0 ^ 5 * y0 ^ 5) ≤ 70 ^ 5 * (K0 ^ 5 * y0 ^ 9) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ p59)
    have e : 100000000 * 70 ^ 5 * K0 ^ 5 * y0 ^ 9 = 100000000 * (70 ^ 5 * (K0 ^ 5 * y0 ^ 9)) := by ring
    rw [e]
    calc _ ≤ _ := h1
      _ ≤ 100000000 * (10 * X + 60) ^ 5 := Nat.mul_le_mul_left _ h2
      _ ≤ 100000000 * (70 ^ 5 * (K0 ^ 5 * y0 ^ 5)) := Nat.mul_le_mul_left _ x5
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  -- the cell capacity `c = A₁·y₀³`
  set c := A1P K0 * y0 ^ 3 with hc
  have hA1 : A1P K0 = 100000000 * K0 ^ 3 + 1000 := rfl
  have ec : c = 100000000 * (K0 ^ 3 * y0 ^ 3) + 1000 * y0 ^ 3 := by rw [hc, hA1]; ring
  have hK3y : K0 * y0 ≤ K0 ^ 3 * y0 ^ 3 := Nat.mul_le_mul hK3 p3
  have hXc : X ≤ c := by rw [ec, hXd]; omega
  have hcap1 : 100 * X + 300 ≤ c := by rw [ec, hXd]; omega
  -- the per-unit cost
  have hA2 : A2P K0 = 1000000 * (A1P K0 + 1) ^ 3 + 100000000 * 70 ^ 5 * K0 ^ 5 + 300 * (A1P K0 + 1) ^ 2 +
      1000000 * K0 ^ 3 + 10000 * K0 + 10000 := rfl
  have h2 : c + 1 ≤ (A1P K0 + 1) * y0 ^ 3 := by
    have hy3 : 1 ≤ y0 ^ 3 := Nat.one_le_pow _ _ hy01
    rw [hc, Nat.add_mul, one_mul]
    omega
  have hpc : PopSetupRun.popCost c ≤ 1000000 * (A1P K0 + 1) ^ 3 * y0 ^ 9 := by
    have h1 := PopSetupReady.popCost_le c
    have h3 : (c + 1) ^ 3 ≤ ((A1P K0 + 1) * y0 ^ 3) ^ 3 := Nat.pow_le_pow_left h2 3
    have e : ((A1P K0 + 1) * y0 ^ 3) ^ 3 = (A1P K0 + 1) ^ 3 * y0 ^ 9 := by ring
    rw [e] at h3
    calc _ ≤ _ := h1
      _ ≤ 1000000 * ((A1P K0 + 1) ^ 3 * y0 ^ 9) := Nat.mul_le_mul_left _ h3
      _ = _ := by ring
  have hem : ∀ j, j < X → emitPBound c j (tabLenP Pl L) ≤
      300 * (A1P K0 + 1) ^ 2 * y0 ^ 9 + 1000000 * K0 ^ 3 * y0 ^ 9 + 12 * X + 100 := by
    intro j hj
    unfold emitPBound
    rw [costL_lenOps]
    have h3 : (c + 1) * (c + 1) ≤ (A1P K0 + 1) ^ 2 * y0 ^ 9 := by
      have := Nat.mul_le_mul h2 h2
      have e : (A1P K0 + 1) * y0 ^ 3 * ((A1P K0 + 1) * y0 ^ 3) = (A1P K0 + 1) ^ 2 * y0 ^ 6 := by ring
      rw [e] at this
      exact this.trans (Nat.mul_le_mul_left _ p69)
    have h4 : 30 * (c + 1) * (c + 1) = 30 * ((c + 1) * (c + 1)) := by ring
    have h5 : tabLenP Pl L ≤ 80000 * (K0 ^ 3 * y0 ^ 3) := by
      have := sT
      omega
    have h6 : K0 ^ 3 * y0 ^ 3 ≤ K0 ^ 3 * y0 ^ 9 := Nat.mul_le_mul_left _ p9
    have e1 : 300 * (A1P K0 + 1) ^ 2 * y0 ^ 9 = 300 * ((A1P K0 + 1) ^ 2 * y0 ^ 9) := by ring
    have e2 : 1000000 * K0 ^ 3 * y0 ^ 9 = 1000000 * (K0 ^ 3 * y0 ^ 9) := by ring
    rw [h4, e1, e2]
    omega
  have hy9X : X ≤ K0 * y0 ^ 9 := by
    rw [hXd]; exact Nat.mul_le_mul_left _ (p3.trans p9)
  have hunit : ∀ j < K0 * y0, cpCost (Data.unaryList [0]).length + 1 + (decBoundP (reqP n Pl L).length j + 1 +
      PopSetupRun.popCost c + 1 + tabPrePCost Pl L (PopSetup.popRW Pl) (PopSetup.popRW Pl) + 1 +
        emitPBound c j (tabLenP Pl L)) ≤ A2P K0 * y0 ^ 9 := by
    intro j hj
    have hjX : j < X := by rw [hXd]; exact hj
    have t1 := hem j hjX
    rw [TabW.cpCost_one]
    unfold decBoundP
    rw [hA2]
    have e : (1000000 * (A1P K0 + 1) ^ 3 + 100000000 * 70 ^ 5 * K0 ^ 5 + 300 * (A1P K0 + 1) ^ 2 +
        1000000 * K0 ^ 3 + 10000 * K0 + 10000) * y0 ^ 9 = 1000000 * (A1P K0 + 1) ^ 3 * y0 ^ 9 +
          100000000 * 70 ^ 5 * K0 ^ 5 * y0 ^ 9 + 300 * (A1P K0 + 1) ^ 2 * y0 ^ 9 + 1000000 * K0 ^ 3 * y0 ^ 9 +
          10000 * (K0 * y0 ^ 9) + 10000 * y0 ^ 9 := by ring
    rw [e]
    have hy9 : 1 ≤ y0 ^ 9 := Nat.one_le_pow _ _ hy01
    omega
  -- the scrub capacity
  have hCW : CWP K0 = A1P K0 + A2P K0 + 4000 * K0 + 2000 := rfl
  have eC : CWP K0 * y0 ^ 9 = A1P K0 * y0 ^ 9 + A2P K0 * y0 ^ 9 + 4000 * (K0 * y0 ^ 9) + 2000 * y0 ^ 9 := by
    rw [hCW]; ring
  have hcy : c ≤ A1P K0 * y0 ^ 9 := Nat.mul_le_mul_left _ p9
  have hy9 : 1 ≤ y0 ^ 9 := Nat.one_le_pow _ _ hy01
  refine ⟨by rw [← hXd]; exact hK, by rw [eC]; omega, by rw [eC]; omega, by rw [eC]; omega, fun f off hf ho => ?_,
    by omega, ?_, ?_, by omega, by rw [← hXd]; exact hXc, hunit⟩
  · have := sN' f off hf ho
    rw [ec]
    have : X * X ≤ K0 ^ 3 * y0 ^ 3 := x2
    omega
  · rw [ec]; omega
  · rw [ec]; omega

end NearCubicWires.WireExponent3_5.FinalPass.SymF
