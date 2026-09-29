import Proof.Foundations.Semantics

/-! # Shared mathematical representations (S0)

Realizes the objects that several paper3 lemmas share, each named by the paper quantity it carries:
* `StarParams` and its coordinates: the hypotheses and parameters of `star:partition` (P3:1186-1218), "`2 ≤ r ≤ n/4`,
  `r` even", `s = ⌊log₂(n/r+1)⌋`, `b = 2^s − 1`, `k = rs`, the `rb` blocked coordinates and the error vectors;
* `mixedDifference` and the signed residual indicators `Z^±` of `star:delta` (P3:1224-1233);
* separated equations and signed occurrence lists of `alg:model` and `alg:pullback` (P3:1552-1565, 1636);
* `F2Poly` and `IntExpression`, the `𝔽₂` polynomials and explicit integer expressions of `alg:compiler`
  (P3:1880-1887) and `list:repair` (P3:1418-1421);
* named regular filters and the call mask `M(e,x)` of `lem:primitive` (P3:3072-3081) and `tr:masks` (P3:3432-3453);
* seeds of the polynomial-evaluation families (P3:2150-2156, 2932-2941);
* reference functions for `star:delta` and for the `list:repair` decoder and repaired list (P3:1449, 1463-1477).

The machine-side representations (printer requests and answers, tape encodings) are in `Proof.Wire_3_5.Foundations.Contracts`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires

/-! ## Star parameters and coordinates (`star:partition`, P3:1186-1218) -/

/-- The hypotheses of `star:partition` (P3:1188): `2 ≤ r ≤ n/4`, `r` even. -/
structure StarParams where
  n : ℕ
  r : ℕ
  r_even : Even r
  two_le_r : 2 ≤ r
  four_r_le_n : 4 * r ≤ n

namespace StarParams
variable (P : StarParams)

/-- `s = ⌊log₂(n/r+1)⌋` (P3:1189).  ℕ division is exact: `⌊log₂ x⌋ = ⌊log₂ ⌊x⌋⌋` for `x ≥ 1`. -/
def s : ℕ := Nat.log 2 (P.n / P.r + 1)
/-- `b = 2^s − 1` (P3:1189). -/
def b : ℕ := 2 ^ P.s - 1
/-- `k = rs` (P3:1189), the live width. -/
def k : ℕ := P.r * P.s

theorem r_pos : 0 < P.r := lt_of_lt_of_le (by norm_num) P.two_le_r

theorem b_succ : P.b + 1 = 2 ^ P.s := by
  unfold b; have := Nat.one_le_two_pow (n := P.s); omega

/-- The `rb` blocked coordinates fit (P3:1200). -/
theorem r_mul_b_le : P.r * P.b ≤ P.n := by
  have h1 : 2 ^ P.s ≤ P.n / P.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have h2 : P.b ≤ P.n / P.r := by have := P.b_succ; omega
  calc P.r * P.b ≤ P.r * (P.n / P.r) := Nat.mul_le_mul_left _ h2
    _ ≤ P.n := Nat.mul_div_le P.n P.r

/-- P3:1217, `b + 1 > (n/r + 1)/2`, written without division: `n + r < 2(b+1)r`. -/
theorem n_add_r_lt : P.n + P.r < 2 * (P.b + 1) * P.r := by
  have h1 : P.n / P.r + 1 < 2 ^ (P.s + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : P.n < P.r * (P.n / P.r + 1) := by
    have := Nat.lt_mul_div_succ P.n P.r_pos; simpa [Nat.mul_comm] using this
  rw [P.b_succ]
  have h3 : P.r * (P.n / P.r + 1) + P.r ≤ P.r * 2 ^ (P.s + 1) := by
    have : P.n / P.r + 1 + 1 ≤ 2 ^ (P.s + 1) := h1
    calc P.r * (P.n / P.r + 1) + P.r = P.r * (P.n / P.r + 1 + 1) := by ring
      _ ≤ P.r * 2 ^ (P.s + 1) := Nat.mul_le_mul_left _ this
  have h4 : P.r * 2 ^ (P.s + 1) = 2 * 2 ^ P.s * P.r := by ring
  omega

/-- Coordinate `i` of block `j` (P3:1200: `rb` coordinates in `r` disjoint blocks). -/
def blockCoord (j : Fin P.r) (i : Fin P.b) : Fin P.n :=
  ⟨j.val * P.b + i.val, by
    have hj : j.val + 1 ≤ P.r := j.isLt
    have hb := P.r_mul_b_le
    have : j.val * P.b + i.val < (j.val + 1) * P.b := by
      have := i.isLt; nlinarith
    calc j.val * P.b + i.val < (j.val + 1) * P.b := this
      _ ≤ P.r * P.b := Nat.mul_le_mul_right _ hj
      _ ≤ P.n := hb⟩

/-- Left blocks are `0 … r/2−1`, right blocks `r/2 … r−1` (P3:1213 "assign r/2 whole blocks to each side"). -/
def leftBlock (j : Fin (P.r / 2)) : Fin P.r := ⟨j.val, by have := j.isLt; omega⟩
def rightBlock (j : Fin (P.r / 2)) : Fin P.r :=
  ⟨P.r / 2 + j.val, by have := j.isLt; have := P.r_even; omega⟩

/-- One error choice per block, `none` = `0`, `some i` = `e_i` (P3:1191-1192). -/
abbrev Errors := Fin (P.r / 2) → Option (Fin P.b)

/-- The error vector of a side (`u` on the left blocks, `v` on the right; P3:1220-1222). -/
def errorVector (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) : BitInput P.n :=
  fun x => decide (∃ j : Fin (P.r / 2), ∃ i : Fin P.b, e j = some i ∧ P.blockCoord (side j) i = x)

end StarParams

/-- Coordinatewise exclusive-or: addition over `𝔽₂` (P3:1184). -/
def xorInput {n : ℕ} (x y : BitInput n) : BitInput n := fun i => xor (x i) (y i)

/-- `0/1` as an integer. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

/-- The mixed difference `Δ_T(c,u,v) = T(c+u+v) − T(c+u) − T(c+v) + T(c)` (`star:delta`, P3:1224). -/
def mixedDifference {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : ℤ :=
  bitZ (T (xorInput (xorInput c u) v)) - bitZ (T (xorInput c u)) - bitZ (T (xorInput c v)) + bitZ (T c)

/-- The signed residual indicators `Z⁺ = [Δ = 1]`, `Z⁻ = [Δ = −1]` (P3:1231-1233, 2440). -/
def residualPlus {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : Bool := decide (mixedDifference T c u v = 1)
def residualMinus {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : Bool := decide (mixedDifference T c u v = -1)

/-! ## Separated equations and signed occurrence lists (`alg:model`, `alg:pullback`, P3:1552-1565, 1636) -/

/-- An integer separated equation `E(z) = a(z_L) + b(z_R) = 0` with arbitrary evaluable half-scores (P3:1636, 1713). -/
structure SeparatedEquation (ZL ZR : Type) where
  left : ZL → ℤ
  right : ZR → ℤ

def SeparatedEquation.holds {ZL ZR : Type} (E : SeparatedEquation ZL ZR) (zl : ZL) (zr : ZR) : Bool :=
  decide (E.left zl + E.right zr = 0)

/-! ## Boolean polynomials over an atom pool (`alg:compiler`, P3:1880-1887; `list:repair`, P3:1418-1421) -/

/-- A squarefree multilinear `𝔽₂` polynomial given as its monomial list (P3:1885-1886).
Each monomial is a list of atom labels; the value is the parity of the satisfied monomials. -/
abbrev F2Poly (Atom : Type) := List (List Atom)

def F2Poly.eval {Atom : Type} (p : F2Poly Atom) (ρ : Atom → Bool) : Bool :=
  p.foldl (fun acc m => xor acc (m.all ρ)) false

/-- An explicit integer expression `V(z) = Σ_ν c_ν ∏_j p_{ν,j}(z)` (P3:1880-1882): the input to `alg:compiler`. -/
abbrev IntExpression (Atom : Type) := List (ℤ × List (F2Poly Atom))

def IntExpression.eval {Atom : Type} (V : IntExpression Atom) (ρ : Atom → Bool) : ℤ :=
  (V.map fun t => t.1 * (t.2.map fun p => bitZ (p.eval ρ)).prod).sum


/-! ## Masks and named filters (`lem:primitive`, P3:3072-3081; `tr:masks`, P3:3432-3453) -/

/-! ## Seeds (`samp:seed`, P3:2932-2939; `filt:majorant`, P3:2150-2156) -/

/-! ## Executable twins (P25) of two B items -/

end NearCubicWires.WireExponent3_5.Shared
