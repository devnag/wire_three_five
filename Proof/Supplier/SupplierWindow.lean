import Proof.Supplier.SupplierList
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Consecutive-window indicator polynomials

This module gives the explicit characteristic-two interpolation used by the
zero-advice list.  Elementary symmetric polynomials evaluate on Boolean inputs
to binomial coefficients of the Hamming weight.  A shifted Chu--Vandermonde
identity and triangular Newton interpolation therefore realize every function
on one consecutive weight window without division.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierWindow

abbrev 𝔽₂ := ZMod 2

def bitAssignment {arity : ℕ} (active : Finset (Fin arity)) :
    Fin arity → 𝔽₂ :=
  fun coordinate => if coordinate ∈ active then 1 else 0

theorem aeval_esymm_bitAssignment {arity degree : ℕ}
    (active : Finset (Fin arity)) :
    MvPolynomial.aeval (bitAssignment active)
        (MvPolynomial.esymm (Fin arity) 𝔽₂ degree) =
      (Nat.choose active.card degree : 𝔽₂) := by
  classical
  simp only [MvPolynomial.esymm, map_sum, map_prod,
    MvPolynomial.aeval_X]
  have hproduct (subset : Finset (Fin arity)) :
      (∏ coordinate ∈ subset, bitAssignment active coordinate) =
        if subset ⊆ active then 1 else 0 := by
    by_cases hsubset : subset ⊆ active
    · simp only [if_pos hsubset]
      exact Finset.prod_eq_one fun coordinate hcoordinate => by
        simp [bitAssignment, hsubset hcoordinate]
    · simp only [if_neg hsubset]
      obtain ⟨coordinate, hcoordinate, hmissing⟩ :=
        Set.not_subset.mp hsubset
      have hmissingFinset : coordinate ∉ active := by
        simpa using hmissing
      apply Finset.prod_eq_zero hcoordinate
      simp [bitAssignment, hmissingFinset]
  simp_rw [hproduct]
  rw [← Finset.sum_filter]
  have hfilter :
      (powersetCard degree (Finset.univ : Finset (Fin arity))).filter
          (· ⊆ active) =
        powersetCard degree active := by
    ext subset
    simp [and_comm]
  rw [hfilter]
  simp

/-! ## Division-free triangular interpolation -/

/-- Coefficients in the lower-triangular binomial basis.  The diagonal
coefficient is always one, so this construction works in characteristic two
without division or a field inversion. -/
def triangularCoefficient (value : ℕ → 𝔽₂) (degree : ℕ) : 𝔽₂ :=
  value degree -
    ∑ lower : Fin degree,
      (Nat.choose degree lower.val : 𝔽₂) *
        triangularCoefficient value lower.val
termination_by degree
decreasing_by
  exact lower.isLt

theorem triangularCoefficient_interpolates
    (value : ℕ → 𝔽₂) (point : ℕ) :
  ∑ degree ∈ Finset.range (point + 1),
        (Nat.choose point degree : 𝔽₂) *
          triangularCoefficient value degree =
      value point := by
  rw [Finset.sum_range_succ]
  rw [triangularCoefficient]
  have hprefix :
      (∑ degree ∈ Finset.range point,
          (Nat.choose point degree : 𝔽₂) *
            triangularCoefficient value degree) =
        ∑ lower : Fin point,
          (Nat.choose point (lower : ℕ) : 𝔽₂) *
            triangularCoefficient value (lower : ℕ) := by
    exact (Fin.sum_univ_eq_sum_range
      (fun degree =>
        (Nat.choose point degree : 𝔽₂) *
          triangularCoefficient value degree)
      point).symm
  rw [hprefix]
  simp

theorem shiftedChoose_identity
    (weight offset degree : ℕ) (hoffset : offset ≤ weight) :
    ∑ indices ∈ (antidiagonal degree : Finset (ℕ × ℕ)),
        (Nat.choose weight indices.1 : 𝔽₂) *
          ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) =
      (Nat.choose (weight - offset) degree : 𝔽₂) := by
  have hvandermonde :=
    Ring.add_choose_eq (R := ℤ)
      (r := (weight : ℤ)) (s := -(offset : ℤ))
      degree (Commute.all _ _)
  have hdifference :
      (weight : ℤ) + -(offset : ℤ) = ((weight - offset : ℕ) : ℤ) := by
    omega
  rw [hdifference, Ring.choose_natCast] at hvandermonde
  simp_rw [Ring.choose_natCast] at hvandermonde
  have hcast := congrArg (fun result : ℤ => (result : 𝔽₂))
    hvandermonde.symm
  simpa using hcast

/-- The shifted binomial basis element `choose(weight - offset, degree)`,
expanded in ordinary elementary symmetric polynomials.  Integer generalized
binomial coefficients are reduced only after Chu--Vandermonde is applied. -/
noncomputable def shiftedEsymm (arity offset degree : ℕ) :
    MvPolynomial (Fin arity) 𝔽₂ :=
  ∑ indices ∈ (antidiagonal degree : Finset (ℕ × ℕ)),
    MvPolynomial.C
        ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) *
      MvPolynomial.esymm (Fin arity) 𝔽₂ indices.1

theorem aeval_shiftedEsymm {arity offset degree : ℕ}
    (active : Finset (Fin arity)) (hoffset : offset ≤ active.card) :
    MvPolynomial.aeval (bitAssignment active)
        (shiftedEsymm arity offset degree) =
      (Nat.choose (active.card - offset) degree : 𝔽₂) := by
  classical
  unfold shiftedEsymm
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  simp_rw [aeval_esymm_bitAssignment]
  simpa [mul_comm] using
    shiftedChoose_identity active.card offset degree hoffset

/-! ## Consecutive-window indicators -/

def windowDelta (target point : ℕ) : 𝔽₂ :=
  if point = target then 1 else 0

/-- An explicit polynomial for one target weight inside
`[offset, offset + width]`.  Coefficients above `width` are never needed. -/
noncomputable def consecutiveWindowIndicator
    (arity offset width target : ℕ) :
    MvPolynomial (Fin arity) 𝔽₂ :=
  ∑ degree ∈ Finset.range (width + 1),
    MvPolynomial.C
        (triangularCoefficient (windowDelta target) degree) *
      shiftedEsymm arity offset degree

theorem aeval_consecutiveWindowIndicator
    {arity offset width target : ℕ}
    (active : Finset (Fin arity))
    (hlower : offset ≤ active.card)
    (hupper : active.card ≤ offset + width) :
    MvPolynomial.aeval (bitAssignment active)
        (consecutiveWindowIndicator arity offset width target) =
      if active.card = offset + target then 1 else 0 := by
  classical
  unfold consecutiveWindowIndicator
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  simp_rw [aeval_shiftedEsymm active hlower]
  let point := active.card - offset
  have hpoint : point ≤ width := by
    dsimp [point]
    omega
  have htruncate :
      (∑ degree ∈ Finset.range (width + 1),
          (algebraMap 𝔽₂ 𝔽₂)
              (triangularCoefficient (windowDelta target) degree) *
            (Nat.choose point degree : 𝔽₂)) =
        ∑ degree ∈ Finset.range (point + 1),
          (algebraMap 𝔽₂ 𝔽₂)
              (triangularCoefficient (windowDelta target) degree) *
            (Nat.choose point degree : 𝔽₂) := by
    symm
    apply Finset.sum_subset
    · intro degree hdegree
      simp only [Finset.mem_range] at hdegree ⊢
      omega
    · intro degree hdegreeWide hdegreeNarrow
      have hdegreeLarge : point < degree := by
        simp only [Finset.mem_range, not_lt] at hdegreeNarrow
        omega
      simp [Nat.choose_eq_zero_of_lt hdegreeLarge]
  rw [htruncate]
  have hinterpolation :=
    triangularCoefficient_interpolates (windowDelta target) point
  calc
    (∑ degree ∈ Finset.range (point + 1),
        (algebraMap 𝔽₂ 𝔽₂)
            (triangularCoefficient (windowDelta target) degree) *
          (Nat.choose point degree : 𝔽₂)) =
        windowDelta target point := by
      simpa [mul_comm] using hinterpolation
    _ = if active.card = offset + target then 1 else 0 := by
      unfold windowDelta
      dsimp [point]
      have hequivalence :
          active.card - offset = target ↔
            active.card = offset + target := by
        omega
      simp [hequivalence]

/-! ## Syntactic degree and multilinearity -/

end NearCubicWires.SupplierWindow
