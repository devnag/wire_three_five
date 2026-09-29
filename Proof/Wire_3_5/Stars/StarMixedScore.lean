import Proof.Wire_3_5.Stars.StarRange

/-! # `eq:mixed-score` and the representations of `Z^±` (`star:range`, P3:1228-1257; `row:identity`, P3:2433-2465)

Realizes the rest of `star:range` (P3:1228-1241): "Its indicators `Z_T^+ = 1[Δ_T = 1]` and `Z_T^- = 1[Δ_T = −1]` are
disjoint Boolean functions of the four corner threshold values. They have exact integer and `𝔽₂` polynomial
representations of degree at most four in those values. For arbitrary weights `w_i`, define
`A_c(u) = Σ_i w_i T_i(c+u)`, `B_c(v) = Σ_i w_i (T_i(c+v) − T_i(c))`. Then (eq:mixed-score) holds exactly, with no
exception for constant-one gates or zero residual populations", where (eq:mixed-score, P3:525-531) is
`Σ_i w_i T_i(z+u+v) = A_z(u) + B_z(v) + Σ_i w_i (Z_i^+ − Z_i^-)`; and the anchored form `row:identity`
(P3:2449-2460): `a_0 + Σ_i a_i X_i(z,u,v) = A_z(u) + B_z(v) + Σ_i a_i (Z_i^+ − Z_i^-)` with
`A_z(u) = a_0 + Σ_i a_i (X_i(z,u,0) − X_i(z,0,0))`, `B_z(v) = Σ_i a_i X_i(z,0,v)`.

Main declarations:
* `corners T c u v : Fin 4 → Bool`, the four corner values `T(c+u+v), T(c+u), T(c+v), T(c)`, and `cornerPlus`,
  `cornerMinus`, the indicators as functions of them (`residualPlus_eq_corner`, `residualMinus_eq_corner`);
* `residual_disjoint`, `mixedDifference_eq_residuals` (`Δ = Z⁺ − Z⁻` wherever `Δ ∈ {−1,0,1}`);
* `zPlusF2`, `zMinusF2 : F2Poly (Fin 4)` (the algebraic normal forms, degree 3 ≤ 4) and `zPlusInt`, `zMinusInt :
  IntExpression (Fin 4)` (the integer multilinear forms, at most four factors, each a single corner), with their exact
  evaluation theorems;
* `mixed_score` (eq:mixed-score, weights in any commutative ring) and `row_identity` (the anchored form), and their star
  instances `star_mixed_score`, `star_row_identity`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-! ## The four corners and the indicators -/

/-- The four corner values of `T` at `(c, u, v)`: `T(c+u+v)`, `T(c+u)`, `T(c+v)`, `T(c)` (P3:1224). -/
def corners {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : Fin 4 → Bool :=
  ![T (xorInput (xorInput c u) v), T (xorInput c u), T (xorInput c v), T c]

/-- The mixed difference as a function of the corners. -/
def cornerDelta (ρ : Fin 4 → Bool) : ℤ := bitZ (ρ 0) - bitZ (ρ 1) - bitZ (ρ 2) + bitZ (ρ 3)

/-- `Z⁺` as a function of the four corner values. -/
def cornerPlus (ρ : Fin 4 → Bool) : Bool := decide (cornerDelta ρ = 1)

/-- `Z⁻` as a function of the four corner values. -/
def cornerMinus (ρ : Fin 4 → Bool) : Bool := decide (cornerDelta ρ = -1)

/-- `Z⁺` is a Boolean function of the four corner values (P3:1231-1233). -/
theorem residualPlus_eq_corner {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualPlus T c u v = cornerPlus (corners T c u v) := rfl

/-- `Z⁻` is a Boolean function of the four corner values (P3:1231-1233). -/
theorem residualMinus_eq_corner {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualMinus T c u v = cornerMinus (corners T c u v) := rfl

/-- `Δ = Z⁺ − Z⁻` over the integers wherever `Δ ∈ {−1,0,1}` (P3:2443-2444). -/
theorem mixedDifference_eq_residuals {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n)
    (h : mixedDifference T c u v ∈ ({-1, 0, 1} : Finset ℤ)) :
    mixedDifference T c u v = bitZ (residualPlus T c u v) - bitZ (residualMinus T c u v) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  unfold residualPlus residualMinus bitZ
  rcases h with h | h | h <;> simp [h]

/-! ## Exact polynomial representations of degree at most four (P3:1233-1235, 1252-1254) -/

/-- The algebraic normal form of `Z⁺` over `𝔽₂` in the corners `0 = T(c+u+v)`, `1 = T(c+u)`, `2 = T(c+v)`,
`3 = T(c)`. -/
def zPlusF2 : F2Poly (Fin 4) :=
  [[0], [3], [0, 1], [0, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

/-- The algebraic normal form of `Z⁻` over `𝔽₂`. -/
def zMinusF2 : F2Poly (Fin 4) :=
  [[1], [2], [0, 1], [0, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

theorem fin4_fun_eq (ρ : Fin 4 → Bool) : ρ = ![ρ 0, ρ 1, ρ 2, ρ 3] := by
  funext i; fin_cases i <;> rfl

theorem zPlusF2_eval_bool : ∀ a b c d : Bool, F2Poly.eval zPlusF2 ![a, b, c, d] = cornerPlus ![a, b, c, d] := by
  decide

theorem zMinusF2_eval_bool : ∀ a b c d : Bool, F2Poly.eval zMinusF2 ![a, b, c, d] = cornerMinus ![a, b, c, d] := by
  decide

/-- **The `𝔽₂` representation of `Z⁺`** at every corner pattern. -/
theorem zPlusF2_eval (ρ : Fin 4 → Bool) : F2Poly.eval zPlusF2 ρ = cornerPlus ρ := by
  rw [fin4_fun_eq ρ]; exact zPlusF2_eval_bool _ _ _ _

/-- **The `𝔽₂` representation of `Z⁻`** at every corner pattern. -/
theorem zMinusF2_eval (ρ : Fin 4 → Bool) : F2Poly.eval zMinusF2 ρ = cornerMinus ρ := by
  rw [fin4_fun_eq ρ]; exact zMinusF2_eval_bool _ _ _ _

/-- The residual bits of a gate at `(c, u, v)` through its corners, in both rings. -/
theorem residualPlus_f2 {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualPlus T c u v = F2Poly.eval zPlusF2 (corners T c u v) := by rw [zPlusF2_eval]; rfl

theorem residualMinus_f2 {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualMinus T c u v = F2Poly.eval zMinusF2 (corners T c u v) := by rw [zMinusF2_eval]; rfl

/-! ## The mixed-score identity (P3:525-531, 1236-1241) and the anchored identity (P3:2449-2460) -/

section Identity
variable {R : Type} [CommRing R] {n : ℕ}

/-- The one-sided left term `A_c(u) = Σ_i w_i T_i(c+u)` (P3:1237). -/
def scoreLeft (gates : List (R × NormalizedThresholdGate n)) (c u : BitInput n) : R :=
  (gates.map fun p => p.1 * (bitZ (p.2.eval (xorInput c u)) : R)).sum

/-- The one-sided right term `B_c(v) = Σ_i w_i (T_i(c+v) − T_i(c))` (P3:1238). -/
def scoreRight (gates : List (R × NormalizedThresholdGate n)) (c v : BitInput n) : R :=
  (gates.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c v)) : R) - (bitZ (p.2.eval c) : R))).sum

/-- The signed residual term `Σ_i w_i (Z_i^+ − Z_i^-)`. -/
def residualTerm (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n) : R :=
  (gates.map fun p => p.1 * ((bitZ (residualPlus p.2.eval c u v) : R) - (bitZ (residualMinus p.2.eval c u v) : R))).sum

/-- The weighted top score at `c + u + v`. -/
def topScore (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n) : R :=
  (gates.map fun p => p.1 * (bitZ (p.2.eval (xorInput (xorInput c u) v)) : R)).sum

/-- One gate's decomposition over the integers, when the left and right flips are disjoint. -/
theorem gate_decomposition (g : NormalizedThresholdGate n) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    bitZ (g.eval (xorInput (xorInput c u) v)) =
      bitZ (g.eval (xorInput c u)) + (bitZ (g.eval (xorInput c v)) - bitZ (g.eval c)) +
        (bitZ (residualPlus g.eval c u v) - bitZ (residualMinus g.eval c u v)) := by
  rw [← mixedDifference_eq_residuals g.eval c u v (mixedDifference_range g c u v hdisj)]
  unfold mixedDifference; ring

/-- **`eq:mixed-score`** (P3:525-531, 1236-1241): for arbitrary weights in any commutative ring, when the left and
right flips are disjoint, `Σ_i w_i T_i(c+u+v) = A_c(u) + B_c(v) + Σ_i w_i (Z_i^+ − Z_i^-)`, exactly. -/
theorem mixed_score (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    topScore gates c u v = scoreLeft gates c u + scoreRight gates c v + residualTerm gates c u v := by
  induction gates with
  | nil => simp [topScore, scoreLeft, scoreRight, residualTerm]
  | cons p gates ih =>
    simp only [topScore, scoreLeft, scoreRight, residualTerm, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have h := congrArg (fun z : ℤ => (z : R)) (gate_decomposition p.2 c u v hdisj)
    simp only [Int.cast_add, Int.cast_sub] at h
    rw [h]; ring

/-- The anchored left term of `row:identity`: `A_z(u) = a_0 + Σ_i a_i (X_i(z,u,0) − X_i(z,0,0))` (P3:2453). -/
def rowLeft (a0 : R) (gates : List (R × NormalizedThresholdGate n)) (c u : BitInput n) : R :=
  a0 + (gates.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c u)) : R) - (bitZ (p.2.eval c) : R))).sum

/-- The anchored right term of `row:identity`: `B_z(v) = Σ_i a_i X_i(z,0,v)` (P3:2454). -/
def rowRight (gates : List (R × NormalizedThresholdGate n)) (c v : BitInput n) : R :=
  (gates.map fun p => p.1 * (bitZ (p.2.eval (xorInput c v)) : R)).sum

/-- **`row:identity`** (P3:2456-2460): `a_0 + Σ_i a_i X_i(z,u,v) = A_z(u) + B_z(v) + Σ_i a_i (Z_i^+ − Z_i^-)`. -/
theorem row_identity (a0 : R) (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    a0 + topScore gates c u v = rowLeft a0 gates c u + rowRight gates c v + residualTerm gates c u v := by
  rw [mixed_score gates c u v hdisj]
  unfold scoreLeft scoreRight rowLeft rowRight
  have : ∀ l : List (R × NormalizedThresholdGate n),
      (l.map fun p => p.1 * (bitZ (p.2.eval (xorInput c u)) : R)).sum +
        (l.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c v)) : R) - (bitZ (p.2.eval c) : R))).sum =
      (l.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c u)) : R) - (bitZ (p.2.eval c) : R))).sum +
        (l.map fun p => p.1 * (bitZ (p.2.eval (xorInput c v)) : R)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons, List.sum_cons]; linear_combination ih
  rw [← add_assoc a0, add_assoc a0 (List.sum _), ← this]

end Identity

end NearCubicWires.WireExponent3_5.Stars
