import Proof.Wire_3_5.FinalPass.SymF6

/-! # SWf (the SYM words writer's flat tables), part 7: the unit's costs, polynomially

The flat tables writer's unit costs `decBoundP`, PA's POP setup program `popCost cap = O(cap³)`, the table stages
`tabPrePCost` (the walk bank `walkBankCost` and C5's builder `bodyCostL`, `lastCostL`) and the emission
`emitPBound`; its capacity needs are PA's `runNeed`, the builder's `hcapC`, `hO` and the table's length `tabLenP`.
Every one is a fixed polynomial in the flat list's numbers:

* the builder's pieces at atoms `≤ y`: `selStep_le`, `selT_le`, `rowStep_le`, `level_le`, `visit_le`, `body_le`,
  `last_le`, `walk_le`; **`tabPre_le`** (`tabPrePCost ≤ 10^8·y^5` at `y = 2·sideB(rank) + errExp + J + L + 4`);
* **`sizes_le`**: at `M, B, errExp, L ≤ X` (`X ≥ 1`): `y ≤ 10·X + 60`, `runNeed ≤ 4·10^7·X²` (seed and offset `≤ X`),
  `hcapC`'s `≤ 100·X + 300`, `hO`'s and `tabLenP ≤ 10^4·(X+1)^3`.

Paper quantity of the main type: the flat tables writer's unit time and space, polynomial in the flat list's numbers
(list:flatten P3:1505-1520; prim:runtime P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.WireExponent3_5.PrimAsm

section Costs
variable (y : ℕ) (hy : 1 ≤ y)
include hy

theorem selStep_le (lb : ℕ) (h : lb ≤ y) : selStepCost lb ≤ 130 * y := by
  unfold selStepCost; omega

theorem selT_le (lb a : ℕ) (h1 : lb ≤ y) (h2 : a ≤ y) : selTCost lb a ≤ 300 * (y * y) := by
  have s := selStep_le y hy lb h1
  have m : a * (selStepCost lb + 4) ≤ y * (134 * y) := Nat.mul_le_mul h2 (by omega)
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  unfold selTCost
  have e : y * (134 * y) = 134 * (y * y) := by ring
  omega

theorem rowStep_le (lb a : ℕ) (h1 : lb ≤ y) (h2 : a ≤ y) : rowStepCost lb a ≤ 400 * (y * y) := by
  have s := selT_le y hy lb a h1 h2
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  unfold rowStepCost
  omega

theorem level_le (lb a L : ℕ) (h1 : lb ≤ y) (h2 : a ≤ y) (h3 : L ≤ y) : levelCost lb a L ≤ 500 * (y * y * y) := by
  have s := rowStep_le y hy lb a h1 h2
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have yyy : y * y ≤ y * y * y := Nat.le_mul_of_pos_right _ hy
  have m : L * (rowStepCost lb a + 4) ≤ y * (404 * (y * y)) := Nat.mul_le_mul h3 (by omega)
  have e : y * (404 * (y * y)) = 404 * (y * y * y) := by ring
  unfold levelCost
  omega

theorem visit_le (m lb L n : ℕ) (h1 : m ≤ y) (h2 : lb ≤ y) (h3 : L ≤ y) (h4 : n ≤ y) :
    visitLCost m lb L n ≤ 2000 * (y * y * y * y) := by
  have s := level_le y hy lb lb L h2 h2 h3
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have yyy : y * y ≤ y * y * y := Nat.le_mul_of_pos_right _ hy
  have y4 : y * y * y ≤ y * y * y * y := Nat.le_mul_of_pos_right _ hy
  have mm : n * (levelCost lb lb L + 4) ≤ y * (504 * (y * y * y)) := Nat.mul_le_mul h4 (by omega)
  have e : y * (504 * (y * y * y)) = 504 * (y * y * y * y) := by ring
  unfold visitLCost mkSeedCost mkEPCost mkBWCost
  omega

theorem body_le (m lb L nJ R : ℕ) (h1 : m ≤ y) (h2 : lb ≤ y) (h3 : L ≤ y) (h4 : nJ ≤ y) (h5 : R ≤ y) :
    bodyCostL m lb L nJ R ≤ 4000 * (y * y * y * y) := by
  have s := visit_le y hy m lb L nJ h1 h2 h3 h4
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have yyy : y * y ≤ y * y * y := Nat.le_mul_of_pos_right _ hy
  have y4 : y * y * y ≤ y * y * y * y := Nat.le_mul_of_pos_right _ hy
  unfold bodyCostL
  omega

theorem last_le (m lb L nJ n : ℕ) (h1 : m ≤ y) (h2 : lb ≤ y) (h3 : L ≤ y) (h4 : nJ ≤ y) (h5 : n ≤ y) :
    lastCostL m lb L nJ n ≤ 4000 * (y * y * y * y) := by
  have s := visit_le y hy m lb L nJ h1 h2 h3 h4
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have yyy : y * y ≤ y * y * y := Nat.le_mul_of_pos_right _ hy
  have y4 : y * y * y ≤ y * y * y * y := Nat.le_mul_of_pos_right _ hy
  have a1 : nJ * (2 * L + 1) ≤ y * (3 * y) := Nat.mul_le_mul h4 (by omega)
  have a2 : n * (1 + nJ * (2 * L + 1)) ≤ y * (1 + y * (3 * y)) := Nat.mul_le_mul h5 (by omega)
  have e1 : y * (3 * y) = 3 * (y * y) := by ring
  have e2 : y * (1 + y * (3 * y)) = y + 3 * (y * y * y) := by ring
  unfold lastCostL
  omega

theorem walk_le (r n R LW : ℕ) (h1 : r ≤ y) (h2 : n ≤ y) (h3 : R ≤ y) (h4 : LW ≤ y) :
    PrimT.WalkBank.walkBankCost r n R LW ≤ 30000000 * (y * y) := by
  unfold PrimT.WalkBank.walkBankCost
  have h : 160 * n + 2 * r + R + LW + 2 ≤ 166 * y := by omega
  have := Nat.mul_le_mul h h
  have e : 166 * y * (166 * y) = 27556 * (y * y) := by ring
  rw [sq]
  omega

end Costs

/-- The table stages' atom bound. -/
def yOf (Pl : FlatListParams) (L : ℕ) : ℕ := 2 * sideB Pl.base.rank + Pl.errExp + Pl.base.J + L + 4

/-- **The table stages' cost**, polynomially. -/
theorem tabPre_le (Pl : FlatListParams) (L : ℕ) :
    tabPrePCost Pl L (PopSetup.popRW Pl) (PopSetup.popRW Pl) ≤ 100000000 * (yOf Pl L) ^ 5 := by
  set y := yOf Pl L with hyd
  have hy : 1 ≤ y := by rw [hyd]; unfold yOf; omega
  have hrk : Pl.base.rank ≤ Pl.base.J + Nat.clog 2 Pl.M := by
    show max (Nat.clog 2 Pl.B + 9) (Nat.clog 2 Pl.M) ≤ _
    have : Nat.clog 2 Pl.B + 9 = Pl.base.J := rfl
    omega
  have hsd : Pl.base.rank ≤ 2 * sideB Pl.base.rank + 1 := by
    show Pl.base.rank ≤ 2 * ((2 * Pl.base.rank + (Pl.base.rank - 1) + 1) / 2) + 1
    omega
  have aM : sideB Pl.base.rank ≤ y := by rw [hyd]; unfold yOf; omega
  have aR : Pl.base.rank ≤ y := by rw [hyd]; unfold yOf; omega
  have aL : L ≤ y := by rw [hyd]; unfold yOf; omega
  have aJ : Pl.base.J + 1 ≤ y := by rw [hyd]; unfold yOf; omega
  have aN : 2 * (Pl.errExp / 4) ≤ y := by rw [hyd]; unfold yOf; omega
  have aW : PopSetup.popRW Pl ≤ y := by rw [hyd]; unfold yOf PopSetup.popRW; omega
  have w := walk_le y hy _ _ _ _ aM aN aW aW
  have b := body_le y hy _ _ _ _ _ aM aR aL aJ aW
  have l := last_le y hy _ _ _ _ _ aM aR aL aJ aN
  have yy : y ≤ y * y := Nat.le_mul_of_pos_left y hy
  have yyy : y * y ≤ y * y * y := Nat.le_mul_of_pos_right _ hy
  have y4 : y * y * y ≤ y * y * y * y := Nat.le_mul_of_pos_right _ hy
  have y5 : y * y * y * y ≤ y * y * y * y * y := Nat.le_mul_of_pos_right _ hy
  have mm : 2 * (Pl.errExp / 4) * (bodyCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1)
      (PopSetup.popRW Pl) + 3) ≤ y * (4003 * (y * y * y * y)) := Nat.mul_le_mul aN (by omega)
  have e : y * (4003 * (y * y * y * y)) = 4003 * (y * y * y * y * y) := by ring
  have p5 : y ^ 5 = y * y * y * y * y := by ring
  unfold tabPrePCost
  rw [p5]
  omega

/-- **The unit's sizes at the flat list's numbers `≤ X`.** -/
theorem sizes_le (Pl : FlatListParams) (L f off X : ℕ) (hX : 1 ≤ X) (hM : Pl.M ≤ X) (hB : Pl.B ≤ X)
    (hE : Pl.errExp ≤ X) (hL : L ≤ X) (hf : f ≤ X) (ho : off ≤ X) :
    yOf Pl L ≤ 10 * X + 60 ∧
    PopSetupRun.runNeed Pl.M Pl.B Pl.errExp f 0 0 0 0 off L ≤ 40000000 * (X * X) ∧
    8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ 100 * X + 300 ∧
    (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < 10000 * ((X + 1) * (X + 1) * (X + 1)) ∧
    tabLenP Pl L ≤ 10000 * ((X + 1) * (X + 1) * (X + 1)) := by
  have cB : Nat.clog 2 Pl.B ≤ Pl.B := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have cM : Nat.clog 2 Pl.M ≤ Pl.M := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hJ : Pl.base.J ≤ X + 9 := by show Nat.clog 2 Pl.B + 9 ≤ _; omega
  have hrk : Pl.base.rank ≤ X + 9 := by show max (Nat.clog 2 Pl.B + 9) (Nat.clog 2 Pl.M) ≤ _; omega
  have hsb : sideB Pl.base.rank ≤ 2 * Pl.base.rank + 1 := by
    show (2 * Pl.base.rank + (Pl.base.rank - 1) + 1) / 2 ≤ _
    omega
  have xx : X ≤ X * X := Nat.le_mul_of_pos_left X hX
  have b1 : (Pl.base.J + 1) * (2 * L + 1) ≤ (X + 10) * (2 * X + 1) := Nat.mul_le_mul (by omega) (by omega)
  have b2 : (X + 10) * (2 * X + 1) ≤ 20 * ((X + 1) * (X + 1)) := by nlinarith
  have b3 : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) ≤
      (X + 1) * (1 + 20 * ((X + 1) * (X + 1))) := Nat.mul_le_mul (by omega) (by omega)
  have b4 : (X + 1) * (1 + 20 * ((X + 1) * (X + 1))) = (X + 1) + 20 * ((X + 1) * (X + 1) * (X + 1)) := by ring
  have b5 : X + 1 ≤ (X + 1) * (X + 1) * (X + 1) := by nlinarith
  have hr : (4096 * Pl.B + 2) * (4096 * Pl.B + 2) ≤ 4098 * X * (4098 * X) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 4098 * X * (4098 * X) = 16793604 * (X * X) := by ring
  refine ⟨by unfold yOf; omega, ?_, by omega, by omega, ?_⟩
  · unfold PopSetupRun.runNeed
    omega
  · unfold tabLenP FlatListParams.walkLen
    have b6 : (2 * (Pl.errExp / 4) + 1) * ((Pl.base.J + 1) * (2 * L + 1) + 1) ≤
        (X + 1) * (1 + 20 * ((X + 1) * (X + 1))) := Nat.mul_le_mul (by omega) (by omega)
    omega

end NearCubicWires.WireExponent3_5.FinalPass.SymF
