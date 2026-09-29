import Proof.Wire_3_5.FinalPass.TabBd1

/-! # S4 (f1), the tables writer, part 11: the writer's size hypotheses (P3:2036-2101, 3170-3178)

At the call's sizes bounded by `X = K₀·Q^{E₀}` at the writer's dimension `Q = 2^m + 1` (the filter's `len`, `cap`,
`errExp`, the mask lengths, the seed count, and `n + 2 ≤ Q`): the cell capacity `capW = A₁·Q^{E₁}` (C6's FILTER setup
need, the tables' lengths, the request, the loop bound), the per-unit cost `A₂·Q^{E₂}` (the decode, C6's setup bound
at `capW`, the table stages, the emission), the scrub capacity `CW·Q^{E₂}` above both and the boot, the loop bound
`2K₀·Q^{E₀}` past `2·|seeds|`. **`tab_hyps`**: every size hypothesis of `tab_writer`.

Paper quantity of the main type: the writer's time and space, polynomial in the dimension `2^m` (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
open NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.BlockPlatform

section Bounds
variable {W : WalkBankProducer} (F5 : FiltSetupSpec5 W)

/-- The cell capacity's exponent. -/
def E1 (E0 : ℕ) : ℕ := E0 * (F5.Dn + 2)

/-- The cell capacity's coefficient. -/
def A1 (K0 : ℕ) : ℕ := F5.Cn * (6 * K0) ^ F5.Dn + 1100 * K0 ^ 2 + 100 * K0 + 10

/-- The per-unit cost's exponent. -/
def E2 (E0 : ℕ) : ℕ := E1 F5 E0 * (F5.Db + 1) + 4 * E0

/-- The per-unit cost's coefficient. -/
def A2 (K0 : ℕ) : ℕ := 1000 + F5.Cb * (A1 F5 K0 + 1) ^ F5.Db + 50000000 * (150000 * K0) ^ 4 + 20000 * K0 ^ 2

/-- The scrub's coefficient. -/
def CW (K0 : ℕ) : ℕ := A1 F5 K0 + A2 F5 K0 + 4000 * K0 + 2000

theorem cpCost_one : cpCost (Data.unaryList [0]).length = 26 := by
  simp [Data.unaryList, cpCost]

/-- **The writer's size hypotheses** at the call's sizes. -/
theorem tab_hyps (m : ℕ) (FP : GapParams) (n L0 L1 K0 E0 : ℕ) (hQ : n + 2 ≤ 2 ^ m + 1) (hK0 : 1 ≤ K0)
    (hE0 : 1 ≤ E0) (hlen : FP.len ≤ K0 * (2 ^ m + 1) ^ E0) (hcap : FP.cap ≤ K0 * (2 ^ m + 1) ^ E0)
    (herr : FP.errExp ≤ K0 * (2 ^ m + 1) ^ E0) (hL0 : L0 ≤ K0 * (2 ^ m + 1) ^ E0)
    (hL1 : L1 ≤ K0 * (2 ^ m + 1) ^ E0) (hnE : Fintype.card (GapSeed FP) ≤ K0 * (2 ^ m + 1) ^ E0) :
    2 * Fintype.card (GapSeed FP) ≤ UnaryCalc.value E0 (2 * K0) (2 ^ m) ∧
    A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0 + 1 ≤ UnaryCalc.value (E2 F5 E0) (CW F5 K0) (2 ^ m) ∧
    A2 F5 K0 * (2 ^ m + 1) ^ E2 F5 E0 + 1 ≤ UnaryCalc.value (E2 F5 E0) (CW F5 K0) (2 ^ m) ∧
    ShellD.bootCost (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) n 0 0 ≤
      UnaryCalc.value (E2 F5 E0) (CW F5 K0) (2 ^ m) ∧
    (∀ L, L = L0 ∨ L = L1 → F5.need FP.len FP.cap FP.errExp L 0 0 0 (Fintype.card (GapSeed FP)) ≤
      A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0) ∧
    (∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 → (tableWord (filterTable FP e L)).length ≤
      A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0) ∧
    2 * (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length + 2 ≤
      A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0 ∧
    UnaryCalc.value E0 (2 * K0) (2 ^ m) ≤ A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0 ∧
    2 ≤ A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0 ∧
    (∀ j < UnaryCalc.value E0 (2 * K0) (2 ^ m), ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 →
      cpCost (Data.unaryList [0]).length + 1 +
        (decBound (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length j + 1 +
          F5.bound (A1 F5 K0 * (2 ^ m + 1) ^ E1 F5 E0) + 1 + tabPreCost FP L (rulerW FP) (rulerW FP) + 1 +
          emitBound (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length j
            (tableWord (filterTable FP e L)).length) ≤ A2 F5 K0 * (2 ^ m + 1) ^ E2 F5 E0) := by
  have ev : ∀ D C, UnaryCalc.value D C (2 ^ m) = C * (2 ^ m + 1) ^ D := fun D C => rfl
  simp only [ev]
  obtain ⟨Q, hQd⟩ : ∃ q, q = 2 ^ m + 1 := ⟨_, rfl⟩
  rw [← hQd] at hQ hlen hcap herr hL0 hL1 hnE ⊢
  have hQ1 : 1 ≤ Q := by omega
  have hE1 : E1 F5 E0 = E0 * (F5.Dn + 2) := rfl
  have hE2 : E2 F5 E0 = E0 * (F5.Dn + 2) * (F5.Db + 1) + 4 * E0 := rfl
  have pw : ∀ a b, a ≤ b → Q ^ a ≤ Q ^ b := fun a b h => Nat.pow_le_pow_right hQ1 h
  obtain ⟨y0, hy0⟩ : ∃ y, y = Q ^ E0 := ⟨_, rfl⟩
  obtain ⟨y1, hy1⟩ : ∃ y, y = Q ^ E1 F5 E0 := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y, y = Q ^ E2 F5 E0 := ⟨_, rfl⟩
  rw [← hy0] at hlen hcap herr hL0 hL1 hnE ⊢
  rw [← hy1, ← hy2]
  have y01 : y0 ≤ y1 := by rw [hy0, hy1]; exact pw _ _ (by rw [hE1]; exact Nat.le_mul_of_pos_right E0 (by omega))
  have y12 : y1 ≤ y2 := by
    rw [hy1, hy2]
    exact pw _ _ (by rw [hE1, hE2]; exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_right _ (by omega)))
  have hy0Q : Q ≤ y0 := by
    rw [hy0]
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ E0 := pw _ _ hE0
  have y2sq : y0 * y0 ≤ y1 := by rw [hy0, hy1, ← pow_add]; exact pw _ _ (by rw [hE1, Nat.mul_add]; omega)
  have y4 : y0 * y0 * (y0 * y0) ≤ y2 := by
    rw [hy0, hy2]
    simp only [← pow_add]
    exact pw _ _ (by rw [hE2]; omega)
  have hy1d : y0 ^ F5.Dn ≤ y1 := by
    rw [hy0, hy1, ← pow_mul]; exact pw _ _ (by rw [hE1]; exact Nat.mul_le_mul_left _ (by omega))
  have hy2b : y1 ^ F5.Db ≤ y2 := by
    rw [hy1, hy2, ← pow_mul]
    exact pw _ _ (by rw [hE1, hE2]; exact Nat.le_add_right_of_le (Nat.mul_le_mul_left _ (by omega)))
  have hy01 : 1 ≤ y0 := by omega
  have hy11 : 1 ≤ y1 := by omega
  have hy21 : 1 ≤ y2 := by omega
  -- the atom `X = K₀·Q^{E₀}`
  obtain ⟨X, hXd⟩ : ∃ x, x = K0 * y0 := ⟨_, rfl⟩
  rw [← hXd] at hlen hcap herr hL0 hL1 hnE
  have hy0K : y0 ≤ X := by rw [hXd]; exact Nat.le_mul_of_pos_left y0 hK0
  have hX2 : 2 ≤ X := by omega
  have hnX : n + 2 ≤ X := by omega
  have hX1 : X ≤ K0 * y1 := by rw [hXd]; exact Nat.mul_le_mul_left _ y01
  have hX2' : X ≤ K0 * y2 := hX1.trans (Nat.mul_le_mul_left _ y12)
  have hXX : X * X ≤ K0 ^ 2 * y1 := by
    rw [hXd, show K0 * y0 * (K0 * y0) = K0 ^ 2 * (y0 * y0) by ring]
    exact Nat.mul_le_mul_left _ y2sq
  have hXX2 : X * X ≤ K0 ^ 2 * y2 := hXX.trans (Nat.mul_le_mul_left _ y12)
  have hX4 : X * X * (X * X) ≤ K0 ^ 4 * y2 := by
    rw [hXd, show K0 * y0 * (K0 * y0) * (K0 * y0 * (K0 * y0)) = K0 ^ 4 * (y0 * y0 * (y0 * y0)) by ring]
    exact Nat.mul_le_mul_left _ y4
  have hK2 : K0 ≤ K0 ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left K0 hK0
  have hwl : ∀ L, L = L0 ∨ L = L1 → L ≤ X := fun L hL => by rcases hL with rfl | rfl <;> assumption
  -- the request word and the tables
  have hw := reqT_le n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP)) X hnX hlen hcap herr hL0 hL1 hnE
  have htw : ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 → (tableWord (filterTable FP e L)).length ≤
      1100 * (X * X) := fun e L hL => tw_le FP e L X (hwl L hL) herr hX2
  -- the cell capacity
  have hA1 : A1 F5 K0 = F5.Cn * (6 * K0) ^ F5.Dn + 1100 * K0 ^ 2 + 100 * K0 + 10 := rfl
  have hneed : ∀ L, L = L0 ∨ L = L1 → F5.need FP.len FP.cap FP.errExp L 0 0 0 (Fintype.card (GapSeed FP)) ≤
      F5.Cn * (6 * K0) ^ F5.Dn * y1 := fun L hL => by
    have h1 := need_le W F5 FP.len FP.cap FP.errExp L (Fintype.card (GapSeed FP)) (6 * X)
      (by have := hwl L hL; omega)
    have h2 : (6 * X) ^ F5.Dn ≤ (6 * K0) ^ F5.Dn * y1 := by
      rw [hXd, show 6 * (K0 * y0) = 6 * K0 * y0 by ring, mul_pow]
      exact Nat.mul_le_mul_left _ hy1d
    calc _ ≤ _ := h1
      _ ≤ F5.Cn * ((6 * K0) ^ F5.Dn * y1) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have hcapW : 1100 * (X * X) + 100 * X + 10 ≤ A1 F5 K0 * y1 := by
    rw [hA1]
    have e : (F5.Cn * (6 * K0) ^ F5.Dn + 1100 * K0 ^ 2 + 100 * K0 + 10) * y1 =
        F5.Cn * (6 * K0) ^ F5.Dn * y1 + 1100 * (K0 ^ 2 * y1) + 100 * (K0 * y1) + 10 * y1 := by ring
    rw [e]
    omega
  have hneedW : ∀ L, L = L0 ∨ L = L1 → F5.need FP.len FP.cap FP.errExp L 0 0 0 (Fintype.card (GapSeed FP)) ≤
      A1 F5 K0 * y1 := fun L hL => by
    have := hneed L hL
    rw [hA1]
    have e : (F5.Cn * (6 * K0) ^ F5.Dn + 1100 * K0 ^ 2 + 100 * K0 + 10) * y1 =
        F5.Cn * (6 * K0) ^ F5.Dn * y1 + (1100 * K0 ^ 2 + 100 * K0 + 10) * y1 := by ring
    rw [e]
    omega
  have hb : 2 * K0 * y0 ≤ A1 F5 K0 * y1 := by
    have : 2 * K0 * y0 = 2 * X := by rw [hXd, Nat.mul_assoc]
    rw [this]; omega
  -- the per-unit cost
  have hA2 : A2 F5 K0 = 1000 + F5.Cb * (A1 F5 K0 + 1) ^ F5.Db + 50000000 * (150000 * K0) ^ 4 +
      20000 * K0 ^ 2 := rfl
  have hbd : F5.bound (A1 F5 K0 * y1) ≤ F5.Cb * (A1 F5 K0 + 1) ^ F5.Db * y2 := by
    have h1 := bound_le W F5 (A1 F5 K0 * y1) ((A1 F5 K0 + 1) * y1) (by rw [Nat.add_mul, one_mul]; omega)
    have h2 : ((A1 F5 K0 + 1) * y1) ^ F5.Db ≤ (A1 F5 K0 + 1) ^ F5.Db * y2 := by
      rw [mul_pow]; exact Nat.mul_le_mul_left _ hy2b
    calc _ ≤ _ := h1
      _ ≤ F5.Cb * ((A1 F5 K0 + 1) ^ F5.Db * y2) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have htp : ∀ L, L = L0 ∨ L = L1 → tabPreCost FP L (rulerW FP) (rulerW FP) ≤
      50000000 * (150000 * K0) ^ 4 * y2 := fun L hL => by
    have h1 := tabPre_le FP L (5 * X) (by have := hwl L hL; omega)
    have h2 : (30000 * (5 * X)) ^ 4 ≤ (150000 * K0) ^ 4 * y2 := by
      rw [show 30000 * (5 * X) = 150000 * X by ring, mul_pow, mul_pow]
      have : X ^ 4 = X * X * (X * X) := by ring
      rw [this]
      calc 150000 ^ 4 * (X * X * (X * X)) ≤ 150000 ^ 4 * (K0 ^ 4 * y2) := Nat.mul_le_mul_left _ hX4
        _ = _ := by ring
    calc _ ≤ _ := h1
      _ ≤ 50000000 * ((150000 * K0) ^ 4 * y2) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have hunit : ∀ j < 2 * K0 * y0, ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 →
      cpCost (Data.unaryList [0]).length + 1 +
        (decBound (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length j + 1 +
          F5.bound (A1 F5 K0 * y1) + 1 + tabPreCost FP L (rulerW FP) (rulerW FP) + 1 +
          emitBound (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length j
            (tableWord (filterTable FP e L)).length) ≤ A2 F5 K0 * y2 := by
    intro j hj e L hL
    have hjX : j < 2 * X := by rw [hXd, ← Nat.mul_assoc]; exact hj
    have t1 := htw e L hL
    have t2 := htp L hL
    rw [cpCost_one]
    unfold decBound emitBound
    rw [hA2]
    have e1 : (1000 + F5.Cb * (A1 F5 K0 + 1) ^ F5.Db + 50000000 * (150000 * K0) ^ 4 + 20000 * K0 ^ 2) * y2 =
        1000 * y2 + F5.Cb * (A1 F5 K0 + 1) ^ F5.Db * y2 + 50000000 * (150000 * K0) ^ 4 * y2 +
          20000 * (K0 ^ 2 * y2) := by ring
    rw [e1]
    have hK2y : K0 * y2 ≤ K0 ^ 2 * y2 := Nat.mul_le_mul_right _ hK2
    omega
  -- the scrub capacity
  have hCW : CW F5 K0 = A1 F5 K0 + A2 F5 K0 + 4000 * K0 + 2000 := rfl
  have hC : ∀ v, v ≤ (A1 F5 K0 + A2 F5 K0 + 4000 * K0 + 2000) * y2 →
      v ≤ CW F5 K0 * y2 := fun v h => by rw [hCW]; exact h
  have eC : (A1 F5 K0 + A2 F5 K0 + 4000 * K0 + 2000) * y2 =
      A1 F5 K0 * y2 + A2 F5 K0 * y2 + 4000 * (K0 * y2) + 2000 * y2 := by ring
  have hA1y : A1 F5 K0 * y1 ≤ A1 F5 K0 * y2 := Nat.mul_le_mul_left _ y12
  have hboot := boot_le (reqT n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) n (16 * X) hw
    (by omega)
  refine ⟨?_, ?_, ?_, ?_, hneedW, fun e L hL => ?_, ?_, hb, ?_, hunit⟩
  · have : 2 * Fintype.card (GapSeed FP) ≤ 2 * X := by omega
    rw [hXd, ← Nat.mul_assoc] at this
    exact this
  · apply hC; rw [eC]; omega
  · apply hC; rw [eC]; omega
  · apply hC; rw [eC]; omega
  · have := htw e L hL; omega
  · omega
  · omega

end Bounds

end NearCubicWires.WireExponent3_5.FinalPass.TabW
