import Proof.Wire_3_5.Foundations.S0

/-! # The product-star partition of `star:partition` (P3:1186-1218): definitions

Realizes the construction in the proof of `star:partition` (P3:1199-1218): "Use `rb` coordinates in `r` blocks,
leaving the others unchanged. Let `H` be the `s×b` matrix whose columns are the nonzero vectors of `𝔽₂^s`. [...]
Every `x∈𝔽₂^b` has exactly one representation `x=c+e`, with `c∈𝒞` and `e∈{0,e_1,…,e_b}`: the syndrome `Hx`
uniquely specifies `e`. The same assertion holds with centers in any fixed coset of `𝒞`. Use all `2^s` cosets in
each block. This gives `2^{rs}` partitions".

Main quantities, all computable:
* `StarParams.column i`: column `i` of `H`, the binary expansion of `i + 1` (so the columns are exactly the nonzero
  vectors of `𝔽₂^s`, since `b = 2^s − 1`);
* `StarParams.syndrome y`: the syndrome `Hy` of one block;
* `StarParams.Translation`: one coset per block, given by its syndrome — the paper's partition index, `2^{rs} = 2^k`
  of them (the "common translation" of `lem:primitive`, P3:3072);
* `StarParams.errorOf σ y`: the unique error `e ∈ {0,e_1,…,e_b}` with `H(y+e) = σ`;
* `StarParams.IsCenter σ c`: `c` is a cell center of the partition `σ`;
* `StarParams.leftErrors`, `rightErrors`, `center`: the decomposition `x = c + u + v` of an input into its cell
  center and its left and right block errors (P3:1220-1222), the coordinates at which the mixed residuals `Δ`, `Z^±`
  of `star:delta` are evaluated;
* `StarParams.translationOfCodes`: a translation read from a list of syndrome codes (a request's word).

The facts about them (the decomposition is a bijection, the cell counts, the uniformity claims) are proved in the
component module `Proof.Wire_3_5.Stars.StarPartition`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires

/-- A vector of `𝔽₂^s`: the syndrome space of one block (P3:1202). -/
abbrev SyndromeVec (s : ℕ) := Fin s → Fin 2

namespace StarParams
variable (P : StarParams)

/-- `s ≥ 1`: `n/r + 1 ≥ 5` (P3:1188). -/
theorem one_le_s : 1 ≤ P.s := by
  unfold s
  have h4 : 4 ≤ P.n / P.r := (Nat.le_div_iff_mul_le P.r_pos).mpr (by have := P.four_r_le_n; omega)
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

theorem b_pos : 0 < P.b := by
  have h := P.b_succ
  have : 2 ^ 1 ≤ 2 ^ P.s := Nat.pow_le_pow_right (by norm_num) P.one_le_s
  omega

theorem column_lt (i : Fin P.b) : i.val + 1 < 2 ^ P.s := by have := P.b_succ; omega

/-- Column `i` of the parity-check matrix `H`: the binary expansion of `i + 1` (P3:1202: "the `s×b` matrix whose
columns are the nonzero vectors of `𝔽₂^s`"). -/
def column (i : Fin P.b) : SyndromeVec P.s := finFunctionFinEquiv.symm ⟨i.val + 1, P.column_lt i⟩

/-- The syndrome `Hy` of one block `y ∈ 𝔽₂^b` (P3:1202-1206). -/
def syndrome (y : Fin P.b → Bool) : SyndromeVec P.s := ∑ i, if y i then P.column i else 0

/-- The error of a block `y` relative to the coset of syndrome `σ`: `none` (`e = 0`) when `Hy = σ`, and otherwise
the coordinate whose column is `Hy − σ` (P3:1204-1206: "the syndrome `Hx` uniquely specifies `e`"). -/
def errorOf (σ : SyndromeVec P.s) (y : Fin P.b → Bool) : Option (Fin P.b) :=
  if P.syndrome y + σ = 0 then none
  else some ⟨(finFunctionFinEquiv (P.syndrome y + σ)).val - 1, by
    have := (finFunctionFinEquiv (P.syndrome y + σ)).isLt
    have := P.b_succ; have := P.b_pos; omega⟩

/-- The bits of block `j` of an input (P3:1200). -/
def blockBits (x : BitInput P.n) (j : Fin P.r) : Fin P.b → Bool := fun i => x (P.blockCoord j i)

/-- **A translation** (the partition index): one coset of the Hamming code in each block, given by its syndrome
(P3:1206-1207: "Use all `2^s` cosets in each block. This gives `2^{rs}` partitions"). -/
abbrev Translation := Fin P.r → SyndromeVec P.s

/-- The cell centers of the partition `σ`: every block lies in its coset (P3:1206-1209). -/
def IsCenter (σ : P.Translation) (c : BitInput P.n) : Prop := ∀ j, P.syndrome (P.blockBits c j) = σ j

instance (σ : P.Translation) : DecidablePred (P.IsCenter σ) := fun c =>
  inferInstanceAs (Decidable (∀ j, P.syndrome (P.blockBits c j) = σ j))

/-- The left block errors `u` of the input `x` in the partition `σ` (P3:1220-1222). -/
def leftErrors (σ : P.Translation) (x : BitInput P.n) : P.Errors :=
  fun j => P.errorOf (σ (P.leftBlock j)) (P.blockBits x (P.leftBlock j))

/-- The right block errors `v` of the input `x` in the partition `σ`. -/
def rightErrors (σ : P.Translation) (x : BitInput P.n) : P.Errors :=
  fun j => P.errorOf (σ (P.rightBlock j)) (P.blockBits x (P.rightBlock j))

/-- The cell center `c` of the input `x` in the partition `σ`: `x = c + u + v` (P3:1204-1206, 1220-1222). -/
def center (σ : P.Translation) (x : BitInput P.n) : BitInput P.n :=
  xorInput (xorInput x (P.errorVector P.leftBlock (P.leftErrors σ x))) (P.errorVector P.rightBlock (P.rightErrors σ x))

/-- The input with cell center `c` and block errors `u, v`: the corner `c + u + v` of `star:delta` (P3:1224). -/
def point (c : BitInput P.n) (u v : P.Errors) : BitInput P.n :=
  xorInput (xorInput c (P.errorVector P.leftBlock u)) (P.errorVector P.rightBlock v)

/-- A translation read from syndrome codes (block `j` gets the binary expansion of the `j`-th code modulo `2^s`),
the form in which a request's word carries it. -/
def translationOfCodes (codes : List ℕ) : P.Translation :=
  fun j => finFunctionFinEquiv.symm ⟨codes.getD j.val 0 % 2 ^ P.s, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

end StarParams

end NearCubicWires.WireExponent3_5.Shared
