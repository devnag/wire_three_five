import Proof.Circuits.CanonicalWitnessCodec
import Proof.Foundations.ComponentwiseValidity

/-!
# Canonical degree-four verifier polynomials

The componentwise verifier reduces every validity, second-moment, and clause
test to one occurrence-sensitive list of monomials.  A monomial carries at
most four normalized atoms, so its expectation is exactly one Fourfold
supplier request.  Keeping coefficients and factor occurrences in lists
prevents an optimizer from silently merging calls or changing the error mass.
-/

open scoped BigOperators

namespace NearCubicWires.ComponentwisePolynomial

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.SupplierPipeline

structure CircuitMonomial (Circuit : Type) (degree : ℕ) where
  coefficient : ℚ
  factors : List Circuit
  degree_le : factors.length ≤ degree

structure CircuitPolynomial (Circuit : Type) (degree : ℕ) where
  monomials : List (CircuitMonomial Circuit degree)

def CircuitMonomial.value
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (monomial : CircuitMonomial Circuit degree)
    (input : BitInput q) : ℝ :=
  (monomial.coefficient : ℝ) *
    bitAsReal (conjunctionBit evaluate monomial.factors input)

def CircuitPolynomial.value
    {Circuit : Type} {degree q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (polynomial : CircuitPolynomial Circuit degree)
    (input : BitInput q) : ℝ :=
  (polynomial.monomials.map fun monomial =>
    monomial.value evaluate input).sum

def CircuitPolynomial.coefficientMass
    {Circuit : Type} {degree : ℕ}
    (polynomial : CircuitPolynomial Circuit degree) : ℚ :=
  (polynomial.monomials.map fun monomial => |monomial.coefficient|).sum

def CircuitMonomial.weaken
    {Circuit : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (monomial : CircuitMonomial Circuit sourceDegree) :
    CircuitMonomial Circuit targetDegree where
  coefficient := monomial.coefficient
  factors := monomial.factors
  degree_le := monomial.degree_le.trans hdegree

def CircuitPolynomial.weaken
    {Circuit : Type} {sourceDegree targetDegree : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (polynomial : CircuitPolynomial Circuit sourceDegree) :
    CircuitPolynomial Circuit targetDegree where
  monomials := polynomial.monomials.map (CircuitMonomial.weaken hdegree)

@[simp] theorem CircuitMonomial.weaken_value
    {Circuit : Type} {sourceDegree targetDegree q : ℕ}
    (hdegree : sourceDegree ≤ targetDegree)
    (evaluate : Circuit → BitInput q → Bool)
    (monomial : CircuitMonomial Circuit sourceDegree)
    (input : BitInput q) :
    (monomial.weaken hdegree).value evaluate input =
      monomial.value evaluate input := rfl

def CircuitPolynomial.constant
    {Circuit : Type} (degree : ℕ) (coefficient : ℚ) :
    CircuitPolynomial Circuit degree where
  monomials :=
    [{ coefficient := coefficient
       factors := []
       degree_le := by simp }]

def CircuitPolynomial.add
    {Circuit : Type} {degree : ℕ}
    (left right : CircuitPolynomial Circuit degree) :
    CircuitPolynomial Circuit degree where
  monomials := left.monomials ++ right.monomials

def CircuitMonomial.scale
    {Circuit : Type} {degree : ℕ} (scalar : ℚ)
    (monomial : CircuitMonomial Circuit degree) :
    CircuitMonomial Circuit degree where
  coefficient := scalar * monomial.coefficient
  factors := monomial.factors
  degree_le := monomial.degree_le

def CircuitPolynomial.scale
    {Circuit : Type} {degree : ℕ} (scalar : ℚ)
    (polynomial : CircuitPolynomial Circuit degree) :
    CircuitPolynomial Circuit degree where
  monomials := polynomial.monomials.map (CircuitMonomial.scale scalar)

def CircuitMonomial.mul
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitMonomial Circuit leftDegree)
    (right : CircuitMonomial Circuit rightDegree) :
    CircuitMonomial Circuit (leftDegree + rightDegree) where
  coefficient := left.coefficient * right.coefficient
  factors := left.factors ++ right.factors
  degree_le := by
    simp only [List.length_append]
    exact Nat.add_le_add left.degree_le right.degree_le

def CircuitPolynomial.mul
    {Circuit : Type} {leftDegree rightDegree : ℕ}
    (left : CircuitPolynomial Circuit leftDegree)
    (right : CircuitPolynomial Circuit rightDegree) :
    CircuitPolynomial Circuit (leftDegree + rightDegree) where
  monomials :=
    left.monomials.flatMap fun leftMonomial =>
      right.monomials.map leftMonomial.mul

def auxiliaryValidityPolynomial
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 4 :=
  let square := linear.mul linear
  let cube := square.mul linear
  let fourth := square.mul square
  (square.weaken (by omega)).add <|
    (cube.weaken (by omega)).scale (-2) |>.add fourth

def atomPolynomial {Circuit : Type} (circuit : Circuit) :
    CircuitPolynomial Circuit 1 where
  monomials :=
    [{ coefficient := 1
       factors := [circuit]
       degree_le := by simp }]

def systematicValidityPolynomial
    {Circuit : Type} (systematic : Circuit)
    (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 2 :=
  let encoded := atomPolynomial systematic
  encoded.weaken (by omega) |>.add <|
    (encoded.mul linear).scale (-2) |>.add (linear.mul linear)

def secondMomentPolynomial
    {Circuit : Type} (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 2 :=
  linear.mul linear

def literalPolynomial
    {Circuit : Type} (negative : Bool)
    (linear : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 1 :=
  if negative then
    (CircuitPolynomial.constant 1 1).add (linear.scale (-1))
  else
    linear

def clausePolynomial
    {Circuit : Type} (leftNegative rightNegative : Bool)
    (left right : CircuitPolynomial Circuit 1) :
    CircuitPolynomial Circuit 2 :=
  let leftLiteral := literalPolynomial leftNegative left
  let rightLiteral := literalPolynomial rightNegative right
  (leftLiteral.weaken (by omega)).add <|
    (rightLiteral.weaken (by omega)).add <|
      (leftLiteral.mul rightLiteral).scale (-1)

end NearCubicWires.ComponentwisePolynomial
