import Proof.Wire_3_5.Primitive.Writers.CallIndexBase
import Proof.Wire_3_5.Primitive.Writers.SymQ

/-! # PA (e), part 1: the call's counts with `c_r`-free exponents

`prim:runtime` (P3:3114-3115): "All powers of `n` are fixed before a fixed `r` or a positive endpoint coefficient is
chosen." Leaf P's children choose their floors `E₄, E₅` after `fe` and BEFORE the free constants `F` (so before
`c_r`); only the coefficients `c₄, c₅` come after `F`. `CallIndex` bounds the counts by
`n^{2·symZ}` with `symZ` depending on `c_r` (through the cap's exponent); that bound serves but not the class
links. Here every count is `K·N^Z` with `N = n + 2`, the constant `K` a function of `c_r` (it goes into `c₄, c₅`), and
the exponent `Z` a function of the literals `l` and of `fe` ONLY (its arguments say so):

* `cap_leR`: `B_m(n) ≤ capK c_r·N^{capZR l}` (the multiplier `r = 2(⌊log₂ L⌋ + c_r) ≤ (2c_r+2)·N`);
* `gapSeed_leR`, `flatSeed_leR`: the filter's and the list's seeds;
* `symI_leR`, `thrI_leR`: the index counts `I = |T|·(2𝔐)² + 1` of `symCount`, `thrCount`;
* `symCount_leR`, `thrCount_leR`: the sample counts `Q ≤ 2^{(5kh+3)/4}·8192·K·N^{Z+2}`.

Paper quantities of the main types: `SeedFix.symCount`, `SeedFix.thrCount` (`symCount_leR`, `thrCount_leR`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CallIndexR
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.CallIndex

/-! ## Symbolic constants (large literal exponents are never evaluated) -/

def k6 : ℕ := 6000
def k4 : ℕ := 400
def k36 : ℕ := 36

theorem k6_eq : k6 = 6000 := rfl
theorem k4_eq : k4 = 400 := rfl
theorem k36_eq : k36 = 36 := rfl

/-! ## `⌈log₂⌉` of a product and `2^{⌈log₂ x⌉}` -/

theorem clog_mul_le (x y : ℕ) : Nat.clog 2 (x * y) ≤ Nat.clog 2 x + Nat.clog 2 y := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) x) (Nat.le_pow_clog (by norm_num) y)

theorem two_pow_clog_le_two_mul (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hpos : 1 ≤ Nat.clog 2 x := Nat.clog_pos (by norm_num) h
    have e : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by rw [← pow_succ']; congr 1; omega
    simp only [Nat.pred_eq_sub_one] at h1
    omega
  · have hx1 : x = 1 := by omega
    subst hx1; simp

theorem clog_KN_le {N K Z x : ℕ} (hx : x ≤ K * N ^ Z) : Nat.clog 2 x ≤ Nat.clog 2 K + Z * Nat.clog 2 N :=
  le_trans (Nat.clog_mono_right 2 hx) (le_trans (clog_mul_le _ _) (Nat.add_le_add_left (pw_clog le_rfl) _))

/-! ## The cap -/

/-- The multiplier `r = 2(⌊log₂ L⌋ + c_r) ≤ (2c_r + 2)·N`. -/
theorem rowBr_leR (cr n : ℕ) : Ledger.rowBr cr n ≤ (2 * cr + 2) * (n + 2) := by
  have h1 : Nat.log 2 (Ledger.Lq n) ≤ n + 2 := le_trans (Nat.log_le_self 2 _) (Lq_le_N n)
  unfold Ledger.rowBr
  nlinarith

/-- The cap's constant: `c_r` only. -/
def capK (cr : ℕ) : ℕ := (2 * cr + 2) ^ 48

theorem capK_pos (cr : ℕ) : 1 ≤ capK cr := Nat.one_le_pow _ _ (by omega)

/-! ## The seeds -/

/-- The filter seeds' constant (`c_r` only) and exponent (`l`, `fe` only). -/
def gapK (cr : ℕ) : ℕ := (8 * capK cr) ^ k6

theorem gapK_pos (cr : ℕ) : 1 ≤ gapK cr := Nat.one_le_pow _ _ (by have := capK_pos cr; omega)

section Gate

end Gate

/-- The flattened lists' constant (`c_r` only) and exponent (`l` only). -/
def flatK (cr : ℕ) : ℕ := 2 ^ k36 * (16384 * capK cr) ^ 4 * 2 ^ k4

theorem flatK_pos (cr : ℕ) : 1 ≤ flatK cr :=
  Nat.one_le_iff_ne_zero.mpr (by unfold flatK; have := capK_pos cr; positivity)

section Gate2

end Gate2

/-! ## The index counts and the sample counts -/

/-- The SYM index constant (`c_r` only) and exponent (`l`, `fe` only). -/
def symKI (cr : ℕ) : ℕ := gapK cr * flatK cr

theorem symKI_pos (cr : ℕ) : 1 ≤ symKI cr := Nat.mul_le_mul (gapK_pos cr) (flatK_pos cr)

/-- `x·y² + 1 ≤ K·N^{a+2b+1}` from `x ≤ K·N^a`, `y ≤ N^b`, `N ≥ 2`, `K ≥ 1`. -/
theorem idx_mass_le {N K a b x y : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K) (hx : x ≤ K * N ^ a) (hy : y ≤ N ^ b) :
    x * y ^ 2 + 1 ≤ K * N ^ (a + 2 * b + 1) := by
  have hy2 : y ^ 2 ≤ N ^ (2 * b) := by rw [pow_mul']; exact Nat.pow_le_pow_left hy 2
  have hxy : x * y ^ 2 ≤ K * N ^ a * N ^ (2 * b) := Nat.mul_le_mul hx hy2
  have hp : 1 ≤ K * N ^ a * N ^ (2 * b) :=
    Nat.mul_le_mul (Nat.mul_le_mul hK (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (by omega))
  calc x * y ^ 2 + 1 ≤ K * N ^ a * N ^ (2 * b) * 2 := by omega
    _ ≤ K * N ^ a * N ^ (2 * b) * N := Nat.mul_le_mul_left _ hN
    _ = K * N ^ (a + 2 * b + 1) := by rw [pow_add, pow_add, pow_one]; simp only [Nat.mul_assoc]

section Index

/-! ## In terms of the star width `k` -/

end Index

end NearCubicWires.WireExponent3_5.PrimAsm.CallIndexR
