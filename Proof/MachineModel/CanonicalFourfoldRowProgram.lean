import Proof.MachineModel.CanonicalBinaryArithmeticProgram
import Proof.MachineModel.FixedAccuracyDenominatorProgram
import Proof.MachineModel.FourfoldRequestEnvelopeProgram
import Proof.Supplier.SupplierEstimator

/-!
# Canonical executable fourfold rows

This module fixes the raw ABI and the finite-index decoders used by the shared
normalized estimator.  Production code enumerates the explicit mixed-radix
indices below; the `Fintype` views in `SupplierEstimator` remain specifications
used only to prove that this enumeration is the same finite probability space.
-/

namespace NearCubicWires.CanonicalFourfoldRowProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierRadix
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge
open NearCubicWires.VerifiedLinker

/-! ## Computable arithmetic and characteristic-two normalization -/

/-- Integer ceiling of the square root.  Unlike `Real.sqrt` followed by
`Nat.ceil`, this definition is directly executable and uses the verified
floor-square-root primitive only once. -/
def natCeilSqrt (value : ℕ) : ℕ :=
  let root := Nat.sqrt value
  if root * root = value then root else root + 1

theorem le_natCeilSqrt_sq (value : ℕ) :
    value ≤ natCeilSqrt value * natCeilSqrt value := by
  change value ≤
    (if Nat.sqrt value * Nat.sqrt value = value then
      Nat.sqrt value else Nat.sqrt value + 1) *
    (if Nat.sqrt value * Nat.sqrt value = value then
      Nat.sqrt value else Nat.sqrt value + 1)
  split
  · rename_i hperfect
    rw [hperfect]
  · exact (Nat.lt_succ_sqrt value).le

theorem sq_lt_of_lt_natCeilSqrt
    {candidate value : ℕ} (hcandidate : candidate < natCeilSqrt value) :
    candidate * candidate < value := by
  change candidate <
    (if Nat.sqrt value * Nat.sqrt value = value then
      Nat.sqrt value else Nat.sqrt value + 1) at hcandidate
  split at hcandidate
  · rename_i hperfect
    exact hperfect ▸ Nat.mul_self_lt_mul_self hcandidate
  · rename_i himperfect
    have hcandidateRoot : candidate ≤ Nat.sqrt value := by omega
    have hsquareLe :
        candidate * candidate ≤ Nat.sqrt value * Nat.sqrt value :=
      Nat.mul_self_le_mul_self hcandidateRoot
    have hrootSquareLe :
        Nat.sqrt value * Nat.sqrt value ≤ value :=
      Nat.sqrt_le value
    have hrootSquareNe :
        Nat.sqrt value * Nat.sqrt value ≠ value :=
      himperfect
    exact hsquareLe.trans_lt
      (lt_of_le_of_ne hrootSquareLe hrootSquareNe)

theorem natCeilSqrt_eq_ceil_real_sqrt (value : ℕ) :
    natCeilSqrt value = ⌈Real.sqrt (value : ℝ)⌉₊ := by
  apply le_antisymm
  · by_contra hle
    have hstrict :
        ⌈Real.sqrt (value : ℝ)⌉₊ < natCeilSqrt value :=
      Nat.lt_of_not_ge hle
    have hsquareStrict :=
      sq_lt_of_lt_natCeilSqrt hstrict
    have hsqrtUpper :
        Real.sqrt (value : ℝ) ≤
          (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hsquareUpper :
        (value : ℝ) ≤
          (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) ^ 2 :=
      (Real.sqrt_le_left (by positivity)).mp hsqrtUpper
    have hsquareUpperNat :
        value ≤
          ⌈Real.sqrt (value : ℝ)⌉₊ *
            ⌈Real.sqrt (value : ℝ)⌉₊ := by
      have hsquareUpperMul :
          (value : ℝ) ≤
            (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) *
              (⌈Real.sqrt (value : ℝ)⌉₊ : ℝ) := by
        simpa [pow_two] using hsquareUpper
      exact_mod_cast hsquareUpperMul
    exact (not_lt_of_ge hsquareUpperNat) hsquareStrict
  · apply Nat.ceil_le.mpr
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hsquare :
        (value : ℝ) ≤
          (natCeilSqrt value : ℝ) *
            (natCeilSqrt value : ℝ) := by
      exact_mod_cast le_natCeilSqrt_sq value
    simpa [pow_two] using hsquare

/-- Taking an integer ceiling before exact natural ceiling division does not
change the final ceiling.  This is the key bridge from real schedule notation
to the executable integer implementation. -/
theorem ceil_ceilDiv_eq_ceil_div
    (value : ℝ)
    (denominator : ℕ) (hdenominator : 0 < denominator) :
    ⌈value⌉₊ ⌈/⌉ denominator =
      ⌈value / denominator⌉₊ := by
  apply le_antisymm
  · apply (ceilDiv_le_iff_le_mul hdenominator).mpr
    apply Nat.ceil_le.mpr
    have hdenominatorReal : (0 : ℝ) < denominator := by
      exact_mod_cast hdenominator
    have hquotient :
        value / (denominator : ℝ) ≤
          (⌈value / denominator⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hproduct :
        value ≤
          (⌈value / denominator⌉₊ : ℝ) *
            (denominator : ℝ) :=
      (div_le_iff₀ hdenominatorReal).mp hquotient
    have hproductNat :
        ⌈value / denominator⌉₊ * denominator ≥
          ⌈value⌉₊ := by
      apply Nat.ceil_le.mpr
      simpa only [Nat.cast_mul] using hproduct
    simpa [mul_comm] using hproductNat
  · apply Nat.ceil_le.mpr
    have hceilProduct :
        ⌈value⌉₊ ≤
          denominator * (⌈value⌉₊ ⌈/⌉ denominator) :=
      (ceilDiv_le_iff_le_mul hdenominator).mp le_rfl
    have hvalueCeil : value ≤ (⌈value⌉₊ : ℝ) := Nat.le_ceil _
    have hdenominatorReal : (0 : ℝ) < denominator := by
      exact_mod_cast hdenominator
    apply (div_le_iff₀ hdenominatorReal).mpr
    have hproductReal :
        value ≤
          (denominator : ℝ) *
            (⌈value⌉₊ ⌈/⌉ denominator : ℕ) :=
      hvalueCeil.trans (by exact_mod_cast hceilProduct)
    simpa [mul_comm] using hproductReal

/-- Executable form of the graded window.  The square root is rounded only
after scaling by 64, then divided with the canonical natural ceiling
division.  This is algebraically the same order of rounding as the real
formula in `gradedWindow`; its refinement theorem below is the only bridge
back to reals. -/
def executableGradedWindow
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) : ℕ :=
  64 +
    (natCeilSqrt (64 ^ 2 * activeBound) ⌈/⌉
      (2 ^ (level.val / 3))
    )

theorem executableGradedWindow_eq_gradedWindow
    (activeBound : ℕ) {depth : ℕ} (level : Fin depth) :
    executableGradedWindow activeBound level =
      gradedWindow activeBound level := by
  let denominator := 2 ^ (level.val / 3)
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hdenominatorCast :
      (denominator : ℝ) =
        (2 : ℝ) ^ (level.val / 3) := by
    dsimp [denominator]
    push_cast
    rfl
  have hscaledSqrt :
      Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) =
        64 * Real.sqrt (activeBound : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (by positivity)]
    norm_num
  have hschedule :
      (64 : ℝ) *
          (Real.sqrt activeBound / denominator + 1) =
        Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) /
            denominator +
          64 := by
    rw [hscaledSqrt]
    ring
  unfold executableGradedWindow gradedWindow
  rw [← hdenominatorCast]
  change
    64 +
        (natCeilSqrt (64 ^ 2 * activeBound) ⌈/⌉ denominator) =
      ⌈(64 : ℝ) *
        (Real.sqrt activeBound / denominator + 1)⌉₊
  rw [natCeilSqrt_eq_ceil_real_sqrt]
  rw [ceil_ceilDiv_eq_ceil_div
    (Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ))
    denominator hdenominator]
  rw [hschedule]
  change
    64 +
        ⌈Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) /
          (denominator : ℝ)⌉₊ =
      ⌈Real.sqrt ((64 ^ 2 * activeBound : ℕ) : ℝ) /
          (denominator : ℝ) + ((64 : ℕ) : ℝ)⌉₊
  rw [Nat.ceil_add_natCast (by positivity) 64]
  omega

/-- A monomial is a sorted list of variable codes.  Repetition is retained:
it represents an exponent, while ordering is erased by multiplication. -/
abbrev EncodedGF2Monomial := List ℕ

/-- A structural polynomial records one entry per coefficient occurrence.
Duplicate monomials therefore cancel when the list is normalized over `𝔽₂`. -/
abbrev StructuralGF2Polynomial := List EncodedGF2Monomial

def structuralGF2Zero : StructuralGF2Polynomial :=
  []

def structuralGF2One : StructuralGF2Polynomial :=
  [[]]

def structuralGF2Add
    (left right : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  left ++ right

def structuralGF2Mul
    (left right : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  left.flatMap fun leftMonomial =>
    right.map fun rightMonomial => leftMonomial ++ rightMonomial

def structuralGF2Scale
    (coefficient : ZMod 2)
    (polynomial : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  if coefficient = 0 then [] else polynomial

/-- Evaluation is deliberately defined on the structural monomial list, not
through `MvPolynomial.support`.  Multiplicity in the list is coefficient
multiplicity and the final odd test is therefore exactly reduction in
characteristic two. -/
def evaluateStructuralGF2
    (assignment : ℕ → Bool)
    (polynomial : StructuralGF2Polynomial) : Bool :=
  exactPolynomialValue
    (fun code (_row : Unit) (_column : Unit) => assignment code)
    polynomial () ()

@[simp] theorem evaluateStructuralGF2_zero
    (assignment : ℕ → Bool) :
    evaluateStructuralGF2 assignment structuralGF2Zero = false := by
  simp [evaluateStructuralGF2, structuralGF2Zero,
    exactPolynomialValue, polynomialOccurrenceCount]

@[simp] theorem evaluateStructuralGF2_one
    (assignment : ℕ → Bool) :
    evaluateStructuralGF2 assignment structuralGF2One = true := by
  simp [evaluateStructuralGF2, structuralGF2One,
    exactPolynomialValue, polynomialOccurrenceCount, exactMonomialValue]

/-! ## Executable structural list-polynomial compiler -/

def encodeListLiteralVariable
    {depth population : ℕ} :
    ListLiteralVariable depth population → ℕ
  | .terminal coordinate => Nat.pair 0 coordinate.val
  | .delta level slot => Nat.pair (level.val + 1) slot.val

def decodeListLiteralVariable
    (depth population code : ℕ) :
    Option (ListLiteralVariable depth population) :=
  let tagged := Nat.unpair code
  if _hterminal : tagged.1 = 0 then
    if hcoordinate : tagged.2 < population then
      some (.terminal ⟨tagged.2, hcoordinate⟩)
    else
      none
  else if hlevel : tagged.1 - 1 < depth then
    if hslot : tagged.2 < 2 * population then
      some (.delta ⟨tagged.1 - 1, hlevel⟩ ⟨tagged.2, hslot⟩)
    else
      none
  else
    none

@[simp] theorem decodeListLiteralVariable_encode
    {depth population : ℕ}
    (literal : ListLiteralVariable depth population) :
    decodeListLiteralVariable depth population
        (encodeListLiteralVariable literal) =
      some literal := by
  cases literal with
  | terminal coordinate =>
      simp [encodeListLiteralVariable, decodeListLiteralVariable,
        Nat.unpair_pair, coordinate.isLt]
  | delta level slot =>
      simp [encodeListLiteralVariable, decodeListLiteralVariable,
        Nat.unpair_pair, level.isLt, slot.isLt]

def encodedListLiteralBooleanAssignment
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) : Bool :=
  match decodeListLiteralVariable depth population code with
  | some literal =>
      listLiteralBooleanAssignment active label seed literal
  | none => false

/-- Proof-only denotation of one encoded monomial.  Invalid variable codes map
to zero, matching the total Boolean decoder; production evaluation never calls
this noncomputable `MvPolynomial` view. -/
noncomputable def interpretEncodedGF2Monomial
    {depth population : ℕ} (monomial : EncodedGF2Monomial) :
    MvPolynomial (ListLiteralVariable depth population) (ZMod 2) :=
  (monomial.map fun code =>
    match decodeListLiteralVariable depth population code with
    | some literal => MvPolynomial.X literal
    | none => 0).prod

/-- Proof-only denotation of the executable occurrence list. -/
noncomputable def interpretStructuralGF2
    {depth population : ℕ} (polynomial : StructuralGF2Polynomial) :
    MvPolynomial (ListLiteralVariable depth population) (ZMod 2) :=
  (polynomial.map interpretEncodedGF2Monomial).sum

theorem aeval_interpretEncodedGF2Monomial
    {depth population : ℕ}
    (assignment : ListLiteralVariable depth population → Bool)
    (monomial : EncodedGF2Monomial) :
    MvPolynomial.aeval
        (fun literal => ((assignment literal).toNat : ZMod 2))
        (interpretEncodedGF2Monomial monomial) =
      ((monomial.all fun code =>
        match decodeListLiteralVariable depth population code with
        | some literal => assignment literal
        | none => false).toNat : ZMod 2) := by
  induction monomial with
  | nil =>
      simp [interpretEncodedGF2Monomial]
  | cons code monomial ih =>
      change
        MvPolynomial.aeval
            (fun literal => ((assignment literal).toNat : ZMod 2))
            ((match decodeListLiteralVariable depth population code with
              | some literal => MvPolynomial.X literal
              | none => 0) *
              interpretEncodedGF2Monomial monomial) =
          ((match decodeListLiteralVariable depth population code with
            | some literal => assignment literal
            | none => false) &&
            (monomial.all fun candidate =>
              match decodeListLiteralVariable depth population candidate with
              | some literal => assignment literal
              | none => false)).toNat
      rw [map_mul, ih]
      cases hdecode :
          decodeListLiteralVariable depth population code with
      | none => simp
      | some literal =>
          cases hvalue : assignment literal <;> simp [hvalue]

theorem aeval_interpretStructuralGF2
    {depth population : ℕ}
    (assignment : ListLiteralVariable depth population → Bool)
    (polynomial : StructuralGF2Polynomial) :
    MvPolynomial.aeval
        (fun literal => ((assignment literal).toNat : ZMod 2))
        (interpretStructuralGF2 polynomial) =
      (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) =>
          match decodeListLiteralVariable depth population code with
          | some literal => assignment literal
          | none => false)
        polynomial () () : ZMod 2) := by
  induction polynomial with
  | nil =>
      simp [interpretStructuralGF2, polynomialOccurrenceCount]
  | cons monomial polynomial ih =>
      change
        MvPolynomial.aeval
            (fun literal => ((assignment literal).toNat : ZMod 2))
            (interpretEncodedGF2Monomial monomial +
              interpretStructuralGF2 polynomial) =
          ((exactMonomialValue
              (fun code (_row : Unit) (_column : Unit) =>
                match decodeListLiteralVariable depth population code with
                | some literal => assignment literal
                | none => false)
              monomial () ()).toNat +
            polynomialOccurrenceCount
              (fun code (_row : Unit) (_column : Unit) =>
                match decodeListLiteralVariable depth population code with
                | some literal => assignment literal
                | none => false)
              polynomial () () : ℕ)
      rw [map_add, aeval_interpretEncodedGF2Monomial, ih]
      unfold exactMonomialValue
      rw [Nat.cast_add]

theorem evaluateStructuralGF2_eq_aeval
    {depth population : ℕ}
    (assignment : ListLiteralVariable depth population → Bool)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2
        (fun code =>
          match decodeListLiteralVariable depth population code with
          | some literal => assignment literal
          | none => false)
        polynomial =
      decide
        (MvPolynomial.aeval
          (fun literal => ((assignment literal).toNat : ZMod 2))
          (interpretStructuralGF2 polynomial) = 1) := by
  unfold evaluateStructuralGF2 exactPolynomialValue
  rw [aeval_interpretStructuralGF2]
  exact decide_eq_decide.mpr ZMod.natCast_eq_one_iff_odd.symm

def structuralGF2Sum
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.flatten

@[simp] theorem interpretStructuralGF2_zero
    {depth population : ℕ} :
    interpretStructuralGF2
        (depth := depth) (population := population) structuralGF2Zero =
      0 := by
  simp [interpretStructuralGF2, structuralGF2Zero]

@[simp] theorem interpretEncodedGF2Monomial_append
    {depth population : ℕ}
    (left right : EncodedGF2Monomial) :
    interpretEncodedGF2Monomial
        (depth := depth) (population := population) (left ++ right) =
      interpretEncodedGF2Monomial left *
        interpretEncodedGF2Monomial right := by
  simp [interpretEncodedGF2Monomial, List.map_append, List.prod_append]

@[simp] theorem interpretStructuralGF2_add
    {depth population : ℕ}
    (left right : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Add left right) =
      interpretStructuralGF2 left + interpretStructuralGF2 right := by
  simp [interpretStructuralGF2, structuralGF2Add, List.map_append,
    List.sum_append]

private theorem interpretStructuralGF2_map_append
    {depth population : ℕ}
    (monomial : EncodedGF2Monomial)
    (polynomial : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (polynomial.map fun right => monomial ++ right) =
      interpretEncodedGF2Monomial monomial *
        interpretStructuralGF2 polynomial := by
  induction polynomial with
  | nil =>
      simp [interpretStructuralGF2]
  | cons right polynomial ih =>
      change
        interpretEncodedGF2Monomial (monomial ++ right) +
            interpretStructuralGF2
              (polynomial.map fun candidate => monomial ++ candidate) =
          interpretEncodedGF2Monomial monomial *
            (interpretEncodedGF2Monomial right +
              interpretStructuralGF2 polynomial)
      rw [interpretEncodedGF2Monomial_append, ih]
      ring

@[simp] theorem interpretStructuralGF2_mul
    {depth population : ℕ}
    (left right : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Mul left right) =
      interpretStructuralGF2 left * interpretStructuralGF2 right := by
  induction left with
  | nil =>
      simp [structuralGF2Mul, interpretStructuralGF2]
  | cons monomial left ih =>
      change
        interpretStructuralGF2
            ((right.map fun rightMonomial => monomial ++ rightMonomial) ++
              structuralGF2Mul left right) =
          (interpretEncodedGF2Monomial monomial +
              interpretStructuralGF2 left) *
            interpretStructuralGF2 right
      rw [show
        interpretStructuralGF2
            ((right.map fun rightMonomial => monomial ++ rightMonomial) ++
              structuralGF2Mul left right) =
          interpretStructuralGF2
              (right.map fun rightMonomial => monomial ++ rightMonomial) +
            interpretStructuralGF2 (structuralGF2Mul left right) by
              exact interpretStructuralGF2_add _ _]
      rw [interpretStructuralGF2_map_append, ih]
      ring

private theorem zmodTwo_eq_one_of_ne_zero
    (coefficient : ZMod 2) (hnonzero : coefficient ≠ 0) :
    coefficient = 1 := by
  apply (ZMod.val_eq_one (by norm_num) coefficient).mp
  have hvalueLt := ZMod.val_lt coefficient
  have hvalueNe : coefficient.val ≠ 0 := by
    intro hzero
    exact hnonzero ((ZMod.val_eq_zero coefficient).mp hzero)
  omega

@[simp] theorem interpretStructuralGF2_scale
    {depth population : ℕ}
    (coefficient : ZMod 2) (polynomial : StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Scale coefficient polynomial) =
      MvPolynomial.C coefficient * interpretStructuralGF2 polynomial := by
  by_cases hzero : coefficient = 0
  · subst coefficient
    rw [show structuralGF2Scale (0 : ZMod 2) polynomial =
      structuralGF2Zero by simp [structuralGF2Scale, structuralGF2Zero]]
    rw [interpretStructuralGF2_zero]
    simp
  · rw [zmodTwo_eq_one_of_ne_zero coefficient hzero]
    simp [structuralGF2Scale]

@[simp] theorem interpretStructuralGF2_sum
    {depth population : ℕ}
    (polynomials : List StructuralGF2Polynomial) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2Sum polynomials) =
      (polynomials.map interpretStructuralGF2).sum := by
  induction polynomials with
  | nil =>
      simp [structuralGF2Sum, interpretStructuralGF2]
  | cons polynomial polynomials ih =>
      change
        interpretStructuralGF2
            (polynomial ++ structuralGF2Sum polynomials) =
          interpretStructuralGF2 polynomial +
            (polynomials.map interpretStructuralGF2).sum
      rw [show
        interpretStructuralGF2
            (polynomial ++ structuralGF2Sum polynomials) =
          interpretStructuralGF2 polynomial +
            interpretStructuralGF2 (structuralGF2Sum polynomials) by
              exact interpretStructuralGF2_add _ _]
      rw [ih]

def structuralGF2Variable (code : ℕ) : StructuralGF2Polynomial :=
  [[code]]

/-- Boolean negation in algebraic normal form over `𝔽₂`. -/
def structuralGF2Not
    (polynomial : StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Add structuralGF2One polynomial

/-- Conjunction of a finite, explicitly ordered polynomial family. -/
def structuralGF2Product
    (polynomials : List StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  polynomials.foldr structuralGF2Mul structuralGF2One

@[simp] theorem exactMonomialValue_append_structural
    (assignment : ℕ → Bool)
    (left right : EncodedGF2Monomial) :
    exactMonomialValue
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (left ++ right) () () =
      (exactMonomialValue
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () () &&
        exactMonomialValue
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () ()) := by
  simp [exactMonomialValue, List.all_append]

theorem polynomialOccurrenceCount_structuralGF2Add
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (structuralGF2Add left right) () () =
      polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () () +
        polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () () := by
  simp [polynomialOccurrenceCount, structuralGF2Add,
    List.map_append, List.sum_append]

private theorem polynomialOccurrenceCount_map_append
    (assignment : ℕ → Bool)
    (left : EncodedGF2Monomial)
    (right : StructuralGF2Polynomial) :
    polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (right.map fun rightMonomial => left ++ rightMonomial) () () =
      (exactMonomialValue
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () ()).toNat *
        polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () () := by
  induction right with
  | nil =>
      simp [polynomialOccurrenceCount]
  | cons right rightPolynomial ih =>
      simp only [List.map_cons, polynomialOccurrenceCount, List.sum_cons]
      rw [exactMonomialValue_append_structural]
      have htail :
          (rightPolynomial.map
              ((fun monomial =>
                (exactMonomialValue
                  (fun code (_row : Unit) (_column : Unit) =>
                    assignment code)
                  monomial () ()).toNat) ∘
                fun rightMonomial => left ++ rightMonomial)).sum =
            (exactMonomialValue
              (fun code (_row : Unit) (_column : Unit) => assignment code)
              left () ()).toNat *
              (rightPolynomial.map
                (fun rightMonomial =>
                  (exactMonomialValue
                    (fun code (_row : Unit) (_column : Unit) =>
                      assignment code)
                    rightMonomial () ()).toNat)).sum := by
        unfold polynomialOccurrenceCount at ih
        rw [List.map_map] at ih
        exact ih
      rw [List.map_map]
      rw [htail]
      cases
          exactMonomialValue
            (fun code (_row : Unit) (_column : Unit) => assignment code)
            left () () <;>
        simp

theorem polynomialOccurrenceCount_structuralGF2Mul
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        (structuralGF2Mul left right) () () =
      polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          left () () *
        polynomialOccurrenceCount
          (fun code (_row : Unit) (_column : Unit) => assignment code)
          right () () := by
  induction left with
  | nil =>
      simp [structuralGF2Mul, polynomialOccurrenceCount]
  | cons leftMonomial leftPolynomial ih =>
      change
        polynomialOccurrenceCount
            (fun code (_row : Unit) (_column : Unit) => assignment code)
            ((right.map fun rightMonomial =>
                leftMonomial ++ rightMonomial) ++
              structuralGF2Mul leftPolynomial right) () () =
          polynomialOccurrenceCount
              (fun code (_row : Unit) (_column : Unit) => assignment code)
              (leftMonomial :: leftPolynomial) () () *
            polynomialOccurrenceCount
              (fun code (_row : Unit) (_column : Unit) => assignment code)
              right () ()
      change
        polynomialOccurrenceCount
            (fun code (_row : Unit) (_column : Unit) => assignment code)
            (structuralGF2Add
              (right.map fun rightMonomial =>
                leftMonomial ++ rightMonomial)
              (structuralGF2Mul leftPolynomial right)) () () =
          _
      rw [polynomialOccurrenceCount_structuralGF2Add]
      rw [polynomialOccurrenceCount_map_append, ih]
      unfold polynomialOccurrenceCount
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.add_mul]

@[simp] theorem evaluateStructuralGF2_variable
    (assignment : ℕ → Bool) (code : ℕ) :
    evaluateStructuralGF2 assignment (structuralGF2Variable code) =
      assignment code := by
  cases hvalue : assignment code <;>
    simp [evaluateStructuralGF2, exactPolynomialValue,
      polynomialOccurrenceCount, exactMonomialValue,
      structuralGF2Variable, hvalue]

@[simp] theorem evaluateStructuralGF2_add
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Add left right) =
      (evaluateStructuralGF2 assignment left !=
        evaluateStructuralGF2 assignment right) := by
  unfold evaluateStructuralGF2 exactPolynomialValue
  rw [polynomialOccurrenceCount_structuralGF2Add]
  simp only [Nat.odd_add, ← Nat.not_odd_iff_even]
  by_cases hleft :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        left () ())
  <;> by_cases hright :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        right () ())
  <;> simp [hleft, hright]

@[simp] theorem evaluateStructuralGF2_mul
    (assignment : ℕ → Bool)
    (left right : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Mul left right) =
      (evaluateStructuralGF2 assignment left &&
        evaluateStructuralGF2 assignment right) := by
  unfold evaluateStructuralGF2 exactPolynomialValue
  rw [polynomialOccurrenceCount_structuralGF2Mul]
  simp only [Nat.odd_mul]
  by_cases hleft :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        left () ())
  <;> by_cases hright :
      Odd (polynomialOccurrenceCount
        (fun code (_row : Unit) (_column : Unit) => assignment code)
        right () ())
  <;> simp [hleft, hright]

@[simp] theorem evaluateStructuralGF2_not
    (assignment : ℕ → Bool)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment (structuralGF2Not polynomial) =
      !(evaluateStructuralGF2 assignment polynomial) := by
  simp [structuralGF2Not]

@[simp] theorem evaluateStructuralGF2_product
    (assignment : ℕ → Bool)
    (polynomials : List StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2Product polynomials) =
      polynomials.all (evaluateStructuralGF2 assignment) := by
  induction polynomials with
  | nil => simp [structuralGF2Product]
  | cons polynomial polynomials ih =>
      change
        evaluateStructuralGF2 assignment
            (structuralGF2Mul polynomial
              (structuralGF2Product polynomials)) =
          _
      rw [evaluateStructuralGF2_mul, ih]
      simp

/-- Capture-avoiding composition of executable structural polynomials.
Variable codes remain natural-number ABI values; `atom` is the sole lowering
map and every source monomial occurrence is retained. -/
def structuralGF2Substitute
    (atom : ℕ → StructuralGF2Polynomial) :
    StructuralGF2Polynomial → StructuralGF2Polynomial
  | [] => structuralGF2Zero
  | monomial :: polynomial =>
      structuralGF2Add
        (structuralGF2Product (monomial.map atom))
        (structuralGF2Substitute atom polynomial)

@[simp] theorem evaluateStructuralGF2_singletonMonomial
    (assignment : ℕ → Bool) (monomial : EncodedGF2Monomial) :
    evaluateStructuralGF2 assignment [monomial] =
      monomial.all assignment := by
  cases hvalue : monomial.all assignment <;>
    simp [evaluateStructuralGF2, exactPolynomialValue,
      polynomialOccurrenceCount, exactMonomialValue, hvalue]

/-- Structural composition is semantically literal substitution on every
Boolean assignment.  This theorem is the bridge used to lower seed-local list
literals into the shared occurrence-residual variables. -/
@[simp] theorem evaluateStructuralGF2_substitute
    (assignment : ℕ → Bool)
    (atom : ℕ → StructuralGF2Polynomial)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2Substitute atom polynomial) =
      evaluateStructuralGF2
        (fun code => evaluateStructuralGF2 assignment (atom code))
        polynomial := by
  induction polynomial with
  | nil =>
      change
        evaluateStructuralGF2 assignment structuralGF2Zero =
          evaluateStructuralGF2
            (fun code => evaluateStructuralGF2 assignment (atom code))
            structuralGF2Zero
      simp
  | cons monomial polynomial ih =>
      rw [structuralGF2Substitute, evaluateStructuralGF2_add,
        evaluateStructuralGF2_product, ih]
      change
        ((monomial.map atom).all (evaluateStructuralGF2 assignment) !=
            evaluateStructuralGF2
              (fun code => evaluateStructuralGF2 assignment (atom code))
              polynomial) =
          evaluateStructuralGF2
            (fun code => evaluateStructuralGF2 assignment (atom code))
            (structuralGF2Add [monomial] polynomial)
      rw [evaluateStructuralGF2_add,
        evaluateStructuralGF2_singletonMonomial]
      simp [Function.comp_def]

/-- Executable parity over a finite coordinate family.  The recursion exposes
the same low-to-high ordering used by every fixed row ABI. -/
def structuralGF2FinParity :
    {arity : ℕ} →
      (Fin arity → StructuralGF2Polynomial) →
        StructuralGF2Polynomial
  | 0, _ => structuralGF2Zero
  | _ + 1, polynomials =>
      structuralGF2Add (polynomials 0)
        (structuralGF2FinParity fun index => polynomials index.succ)

private theorem boolParity_fin_succ
    {arity : ℕ} (value : Fin (arity + 1) → Bool) :
    boolParity value =
      (value 0 != boolParity (fun index : Fin arity => value index.succ)) := by
  unfold boolParity
  rw [Fin.sum_univ_succ]
  cases value 0 <;>
    simp [Nat.odd_add, ← Nat.not_odd_iff_even]

@[simp] theorem evaluateStructuralGF2_finParity
    (assignment : ℕ → Bool) {arity : ℕ}
    (polynomials : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2FinParity polynomials) =
      boolParity fun index =>
        evaluateStructuralGF2 assignment (polynomials index) := by
  induction arity with
  | zero =>
      simp [structuralGF2FinParity, boolParity]
  | succ arity ih =>
      rw [structuralGF2FinParity, evaluateStructuralGF2_add,
        ih, boolParity_fin_succ]

/-- Structural version of the canonical total one-hot lookup.  Only lookup
coordinates whose table entry is true are retained, so this does not expand
to a truth table or introduce a parallel selection path. -/
def structuralGF2OneHotLookup
    {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot :
      Fin (populationBound + 1) → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun candidate =>
    if lookup candidate then oneHot candidate else structuralGF2Zero

@[simp] theorem evaluateStructuralGF2_oneHotLookup
    (assignment : ℕ → Bool)
    {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot :
      Fin (populationBound + 1) → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2OneHotLookup lookup oneHot) =
      oneHotLookupRow lookup fun candidate =>
        evaluateStructuralGF2 assignment (oneHot candidate) := by
  rw [structuralGF2OneHotLookup, evaluateStructuralGF2_finParity]
  unfold oneHotLookupRow
  congr 1
  funext candidate
  cases lookup candidate <;>
    simp

/-- Indicator polynomial for one complete Boolean assignment.  A false target
bit contributes `1 + x`; a true target bit contributes `x`, so the degree is
exactly the source arity and no auxiliary selector variables are introduced. -/
def structuralGF2BooleanSelector
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (target : BitInput arity) :
    StructuralGF2Polynomial :=
  structuralGF2Product <|
    List.ofFn fun index =>
      if target index then bits index
      else structuralGF2Not (bits index)

@[simp] theorem evaluateStructuralGF2_booleanSelector
    (assignment : ℕ → Bool) {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (target : BitInput arity) :
    evaluateStructuralGF2 assignment
        (structuralGF2BooleanSelector bits target) =
      decide
        ((fun index =>
          evaluateStructuralGF2 assignment (bits index)) = target) := by
  rw [structuralGF2BooleanSelector, evaluateStructuralGF2_product]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro hall
    funext index
    have hselected := hall
      (if target index then bits index
        else structuralGF2Not (bits index))
      (List.mem_ofFn.mpr ⟨index, rfl⟩)
    cases htarget : target index <;>
      cases hvalue : evaluateStructuralGF2 assignment (bits index) <;>
      simp_all
  · intro hequal polynomial hmember
    rcases List.mem_ofFn.mp hmember with ⟨index, rfl⟩
    have hindex := congrFun hequal index
    cases htarget : target index <;>
      cases hvalue : evaluateStructuralGF2 assignment (bits index) <;>
      simp_all

/-- Canonical low-to-high decoding of an in-range truth-table row. -/
def structuralTruthAssignment
    (arity : ℕ) (code : Fin (2 ^ arity)) : BitInput arity :=
  fun index => code.val.testBit index.val

@[simp] theorem structuralTruthAssignment_encode
    {arity : ℕ} (assignment : BitInput arity) :
    structuralTruthAssignment arity
        ⟨encodeBitInput assignment, by
          rw [encodeBitInput_eq_ofBits]
          exact Nat.ofBits_lt_two_pow assignment⟩ =
      assignment := by
  funext index
  change (encodeBitInput assignment).testBit index.val = assignment index
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt assignment index.val index.isLt

/-- Algebraic-normal-form truth-table compiler.  It is reserved for
logarithmic-arity fixed Boolean combiners (not population-sized lookups):
the assignment indicators are disjoint, so parity is exactly the requested
function on every input, including malformed upstream rows. -/
def structuralGF2TruthTable
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (function : BitInput arity → Bool) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun code : Fin (2 ^ arity) =>
    if function (structuralTruthAssignment arity code) then
      structuralGF2BooleanSelector bits
        (structuralTruthAssignment arity code)
    else
      structuralGF2Zero

@[simp] theorem evaluateStructuralGF2_truthTable
    (assignment : ℕ → Bool) {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial)
    (function : BitInput arity → Bool) :
    evaluateStructuralGF2 assignment
        (structuralGF2TruthTable bits function) =
      function fun index =>
        evaluateStructuralGF2 assignment (bits index) := by
  let actual : BitInput arity :=
    fun index => evaluateStructuralGF2 assignment (bits index)
  let actualCode : Fin (2 ^ arity) :=
    ⟨encodeBitInput actual, by
      rw [encodeBitInput_eq_ofBits]
      exact Nat.ofBits_lt_two_pow actual⟩
  have hdecodeActual :
      structuralTruthAssignment arity actualCode = actual := by
    exact structuralTruthAssignment_encode actual
  have hdecodeInjective :
      Function.Injective (structuralTruthAssignment arity) := by
    intro left right hequal
    apply Fin.ext
    have hencoded := congrArg encodeBitInput hequal
    unfold structuralTruthAssignment at hencoded
    rw [encodeBitInput_testBit left.isLt,
      encodeBitInput_testBit right.isLt] at hencoded
    exact hencoded
  rw [structuralGF2TruthTable, evaluateStructuralGF2_finParity]
  have hrow :
      (fun code : Fin (2 ^ arity) =>
          evaluateStructuralGF2 assignment
            (if function (structuralTruthAssignment arity code) then
              structuralGF2BooleanSelector bits
                (structuralTruthAssignment arity code)
            else
              structuralGF2Zero)) =
        fun code =>
          decide (code = actualCode) &&
            function (structuralTruthAssignment arity code) := by
    funext code
    rw [apply_ite (evaluateStructuralGF2 assignment)]
    rw [evaluateStructuralGF2_booleanSelector]
    change
      (if function (structuralTruthAssignment arity code) then
          decide (actual = structuralTruthAssignment arity code)
        else false) =
        (decide (code = actualCode) &&
          function (structuralTruthAssignment arity code))
    by_cases hfunction :
        function (structuralTruthAssignment arity code) = true
    · rw [if_pos hfunction]
      simp only [hfunction, Bool.and_true]
      apply decide_eq_decide.mpr
      constructor
      · intro hequal
        apply hdecodeInjective
        rw [hdecodeActual]
        exact hequal.symm
      · intro hequal
        subst code
        exact hdecodeActual.symm
    · have hfalse :=
        Bool.eq_false_of_not_eq_true hfunction
      rw [if_neg hfunction]
      simp [hfalse]
  rw [hrow, boolParity_exactSelector]
  rw [hdecodeActual]

/-- Majority over the walk-time coordinate family.  Only this logarithmic
combiner uses the truth-table compiler; population lookups stay linear via
`structuralGF2OneHotLookup`. -/
def structuralGF2BitMajority
    {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2TruthTable bits compiledBitMajority

@[simp] theorem evaluateStructuralGF2_bitMajority
    (assignment : ℕ → Bool) {arity : ℕ}
    (bits : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2BitMajority bits) =
      compiledBitMajority fun index =>
        evaluateStructuralGF2 assignment (bits index) := by
  exact evaluateStructuralGF2_truthTable
    assignment bits compiledBitMajority

/-- Structural finite conjunction used by the symmetric circuit segments. -/
def structuralGF2FiniteConjunction
    {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2Product (List.ofFn values)

@[simp] theorem evaluateStructuralGF2_finiteConjunction
    (assignment : ℕ → Bool) {arity : ℕ}
    (values : Fin arity → StructuralGF2Polynomial) :
    evaluateStructuralGF2 assignment
        (structuralGF2FiniteConjunction values) =
      finiteBoolConjunction fun index =>
        evaluateStructuralGF2 assignment (values index) := by
  rw [structuralGF2FiniteConjunction, evaluateStructuralGF2_product]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, finiteBoolConjunction_eq_true_iff]
  constructor
  · intro hall index
    exact hall (values index) (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · intro hall value hmember
    rcases List.mem_ofFn.mp hmember with ⟨index, rfl⟩
    exact hall index

/-- Direct executable expansion of an elementary symmetric polynomial.  The
input is a duplicate-free list of variable codes; `sublistsLen` enumerates
exactly the degree-sized subsets without quotienting through `Finset.toList`. -/
def structuralGF2ElementarySymmetric
    (codes : List ℕ) (degree : ℕ) :
    StructuralGF2Polynomial :=
  codes.sublistsLen degree

private theorem sublistsLen_map
    {α β : Type} (mapValue : α → β)
    (degree : ℕ) (values : List α) :
    List.sublistsLen degree (values.map mapValue) =
      (List.sublistsLen degree values).map (List.map mapValue) := by
  induction degree generalizing values with
  | zero =>
      simp [List.sublistsLen_zero]
  | succ degree ih =>
      induction values with
      | nil =>
          simp [List.sublistsLen_succ_nil]
      | cons value values tailIH =>
          rw [List.map_cons, List.sublistsLen_succ_cons,
            List.sublistsLen_succ_cons, tailIH, ih]
          simp [List.map_append, Function.comp_def]

theorem interpretStructuralGF2_elementarySymmetric
    {depth population : ℕ}
    (codes : List ℕ) (degree : ℕ) :
    interpretStructuralGF2
        (depth := depth) (population := population)
        (structuralGF2ElementarySymmetric codes degree) =
      ((codes.map fun code =>
        match decodeListLiteralVariable depth population code with
        | some literal => MvPolynomial.X literal
        | none => 0 : List
          (MvPolynomial (ListLiteralVariable depth population) (ZMod 2))) :
        Multiset
          (MvPolynomial (ListLiteralVariable depth population) (ZMod 2))).esymm
        degree := by
  unfold structuralGF2ElementarySymmetric interpretStructuralGF2
  unfold interpretEncodedGF2Monomial Multiset.esymm
  rw [Multiset.powersetCard_coe]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  rw [sublistsLen_map]
  simp [Function.comp_def, Multiset.prod_coe]

theorem interpretStructuralGF2_elementarySymmetric_ofFn
    {depth population arity : ℕ}
    (embed : Fin arity → ListLiteralVariable depth population)
    (degree : ℕ) :
    interpretStructuralGF2
        (structuralGF2ElementarySymmetric
          (List.ofFn fun coordinate =>
            encodeListLiteralVariable (embed coordinate))
          degree) =
      MvPolynomial.rename embed
        (MvPolynomial.esymm (Fin arity) (ZMod 2) degree) := by
  rw [interpretStructuralGF2_elementarySymmetric]
  simp only [List.map_ofFn, Function.comp_def,
    decodeListLiteralVariable_encode]
  rw [← Fin.univ_val_map]
  rw [Finset.esymm_map_val]
  unfold MvPolynomial.esymm
  simp only [map_sum, map_prod, MvPolynomial.rename_X]

def structuralGF2ShiftedElementarySymmetric
    (codes : List ℕ) (offset degree : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2Sum <|
    (List.Nat.antidiagonal degree).map fun indices =>
      structuralGF2Scale
        ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : ZMod 2)
        (structuralGF2ElementarySymmetric codes indices.1)

theorem interpretStructuralGF2_shiftedElementarySymmetric_ofFn
    {depth population arity : ℕ}
    (embed : Fin arity → ListLiteralVariable depth population)
    (offset degree : ℕ) :
    interpretStructuralGF2
        (structuralGF2ShiftedElementarySymmetric
          (List.ofFn fun coordinate =>
            encodeListLiteralVariable (embed coordinate))
          offset degree) =
      MvPolynomial.rename embed
        (SupplierWindow.shiftedEsymm arity offset degree) := by
  unfold structuralGF2ShiftedElementarySymmetric
  rw [interpretStructuralGF2_sum]
  simp only [List.map_map, Function.comp_def,
    interpretStructuralGF2_scale,
    interpretStructuralGF2_elementarySymmetric_ofFn]
  unfold SupplierWindow.shiftedEsymm
  simp only [map_sum, map_mul, MvPolynomial.rename_C]
  rfl

def structuralGF2ConsecutiveWindowIndicator
    (codes : List ℕ) (offset width target : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2Sum <|
    (List.range (width + 1)).map fun degree =>
      structuralGF2Scale
        (SupplierWindow.triangularCoefficient
          (SupplierWindow.windowDelta target) degree)
        (structuralGF2ShiftedElementarySymmetric
          codes offset degree)

theorem interpretStructuralGF2_consecutiveWindowIndicator_ofFn
    {depth population arity : ℕ}
    (embed : Fin arity → ListLiteralVariable depth population)
    (offset width target : ℕ) :
    interpretStructuralGF2
        (structuralGF2ConsecutiveWindowIndicator
          (List.ofFn fun coordinate =>
            encodeListLiteralVariable (embed coordinate))
          offset width target) =
      MvPolynomial.rename embed
        (SupplierWindow.consecutiveWindowIndicator
          arity offset width target) := by
  unfold structuralGF2ConsecutiveWindowIndicator
  rw [interpretStructuralGF2_sum]
  simp only [List.map_map, Function.comp_def,
    interpretStructuralGF2_scale,
    interpretStructuralGF2_shiftedElementarySymmetric_ofFn]
  unfold SupplierWindow.consecutiveWindowIndicator
  simp only [map_sum, map_mul, MvPolynomial.rename_C]
  rfl

def terminalLiteralVariableCodes
    (depth population : ℕ) : List ℕ :=
  List.ofFn fun coordinate : Fin population =>
    encodeListLiteralVariable
      (ListLiteralVariable.terminal (depth := depth) coordinate)

def deltaLiteralVariableCodes
    {depth population : ℕ} (level : Fin depth) : List ℕ :=
  List.ofFn fun slot : Fin (2 * population) =>
    encodeListLiteralVariable
      (ListLiteralVariable.delta level slot)

def structuralTerminalWindowPolynomial
    (depth population terminalWindow target : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2ConsecutiveWindowIndicator
    (terminalLiteralVariableCodes depth population)
    0 terminalWindow target

theorem interpretStructuralTerminalWindowPolynomial
    (depth population terminalWindow target : ℕ) :
    interpretStructuralGF2
        (structuralTerminalWindowPolynomial
          depth population terminalWindow target) =
      terminalWindowPolynomial depth population terminalWindow target := by
  unfold structuralTerminalWindowPolynomial terminalLiteralVariableCodes
  rw [interpretStructuralGF2_consecutiveWindowIndicator_ofFn]
  rfl

def structuralDeltaWindowPolynomial
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    StructuralGF2Polynomial :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  structuralGF2ConsecutiveWindowIndicator
    (deltaLiteralVariableCodes (population := population) level)
    (childCard - window level) (2 * window level) target

theorem interpretStructuralDeltaWindowPolynomial
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    interpretStructuralGF2
        (structuralDeltaWindowPolynomial
          label seed window level target) =
      deltaWindowPolynomial label seed window level target := by
  unfold structuralDeltaWindowPolynomial deltaLiteralVariableCodes
  unfold deltaWindowPolynomial
  dsimp only
  rw [interpretStructuralGF2_consecutiveWindowIndicator_ofFn]

def structuralDeltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    StructuralGF2Polynomial :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  match deltaTarget? childCard (window level)
      parent.val child.val with
  | none => structuralGF2Zero
  | some target =>
      structuralDeltaWindowPolynomial label seed window level target

theorem interpretStructuralDeltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralDeltaFactor label seed window level parent child) =
      deltaFactor label seed window level parent child := by
  unfold structuralDeltaFactor deltaFactor
  dsimp only
  split <;>
    simp_all [interpretStructuralGF2_zero,
      interpretStructuralDeltaWindowPolynomial]

abbrev StructuralListPolynomialVector (population : ℕ) :=
  Fin (population + 1) → StructuralGF2Polynomial

def structuralTerminalPolynomialVector
    (depth population terminalWindow : ℕ) :
    StructuralListPolynomialVector population :=
  fun candidate =>
    structuralTerminalWindowPolynomial depth population
      terminalWindow candidate.val

theorem interpretStructuralTerminalPolynomialVector
    (depth population terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralTerminalPolynomialVector
          depth population terminalWindow candidate) =
      terminalPolynomialVector depth population terminalWindow candidate := by
  unfold structuralTerminalPolynomialVector terminalPolynomialVector
  exact interpretStructuralTerminalWindowPolynomial
    depth population terminalWindow candidate.val

def structuralCombineListLevel
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population) :
    StructuralListPolynomialVector population :=
  fun parent =>
    structuralGF2Sum <|
      List.ofFn fun child : Fin (population + 1) =>
        structuralGF2Mul (childPolynomials child)
          (structuralDeltaFactor label seed window level parent child)

theorem interpretStructuralCombineListLevel
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population)
    (childSpecification : ListPolynomialVector depth population)
    (hrefines : ∀ child,
      interpretStructuralGF2 (childPolynomials child) =
        childSpecification child)
    (parent : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralCombineListLevel label seed window level
          childPolynomials parent) =
      combineListLevel label seed window level childSpecification parent := by
  unfold structuralCombineListLevel combineListLevel
  rw [interpretStructuralGF2_sum]
  simp only [List.map_ofFn, Function.comp_def,
    interpretStructuralGF2_mul]
  simp_rw [hrefines, interpretStructuralDeltaFactor]
  rw [List.sum_ofFn]

/-- Structural recursion over the remaining levels.  Every constructor is
computable; no `MvPolynomial.support`, quotient enumeration, or classical
choice is present in the production path. -/
def structuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ) :
    StructuralListPolynomialVector population :=
  if hlevel : level < depth then
    structuralCombineListLevel label seed window ⟨level, hlevel⟩
      (structuralListPolynomialVectorFrom label seed window
        terminalWindow (level + 1))
  else
    structuralTerminalPolynomialVector depth population terminalWindow
termination_by depth - level
decreasing_by omega

theorem interpretStructuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralListPolynomialVectorFrom label seed window
          terminalWindow level candidate) =
      listPolynomialVectorFrom label seed window
        terminalWindow level candidate := by
  rw [structuralListPolynomialVectorFrom, listPolynomialVectorFrom]
  by_cases hnext : level < depth
  · rw [dif_pos hnext, dif_pos hnext]
    apply interpretStructuralCombineListLevel label seed window
      ⟨level, hnext⟩ _ _
    intro child
    exact interpretStructuralListPolynomialVectorFrom label seed window
      terminalWindow (level + 1) child
  · rw [dif_neg hnext, dif_neg hnext]
    exact interpretStructuralTerminalPolynomialVector
      depth population terminalWindow candidate
termination_by depth - level
decreasing_by omega

def structuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ) :
    StructuralListPolynomialVector population :=
  structuralListPolynomialVectorFrom label seed window terminalWindow 0

theorem interpretStructuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    interpretStructuralGF2
        (structuralListPolynomialVector label seed window
          terminalWindow candidate) =
      listPolynomialVector label seed window
        terminalWindow candidate := by
  unfold structuralListPolynomialVector listPolynomialVector
  exact interpretStructuralListPolynomialVectorFrom label seed window
    terminalWindow 0 candidate

/-- Total decoder for the doubled literal population.  The left half carries
active sibling coordinates; the right half carries complemented child
coordinates. -/
def decodeListLiteralSlot
    {population : ℕ} (slot : Fin (2 * population)) :
    Sum (Fin population) (Fin population) :=
  if hleft : slot.val < population then
    .inl ⟨slot.val, hleft⟩
  else
    .inr ⟨slot.val - population, by omega⟩

@[simp] theorem decodeListLiteralSlot_left
    {population : ℕ} (coordinate : Fin population) :
    decodeListLiteralSlot (leftLiteralSlot coordinate) =
      .inl coordinate := by
  unfold decodeListLiteralSlot leftLiteralSlot
  rw [dif_pos coordinate.isLt]

@[simp] theorem decodeListLiteralSlot_right
    {population : ℕ} (coordinate : Fin population) :
    decodeListLiteralSlot (rightLiteralSlot coordinate) =
      .inr coordinate := by
  have hright :
      ¬(rightLiteralSlot coordinate).val < population := by
    simp [rightLiteralSlot]
  unfold decodeListLiteralSlot
  rw [dif_neg hright]
  apply congrArg Sum.inr
  apply Fin.ext
  simp [rightLiteralSlot]

private theorem decodeListLiteralSlot_inl
    {population : ℕ} {slot : Fin (2 * population)}
    {coordinate : Fin population}
    (hdecode : decodeListLiteralSlot slot = .inl coordinate) :
    slot = leftLiteralSlot coordinate := by
  unfold decodeListLiteralSlot at hdecode
  split at hdecode
  · simp only [Sum.inl.injEq] at hdecode
    subst coordinate
    apply Fin.ext
    rfl
  · simp at hdecode

private theorem decodeListLiteralSlot_inr
    {population : ℕ} {slot : Fin (2 * population)}
    {coordinate : Fin population}
    (hdecode : decodeListLiteralSlot slot = .inr coordinate) :
    slot = rightLiteralSlot coordinate := by
  unfold decodeListLiteralSlot at hdecode
  split at hdecode
  · simp at hdecode
  · simp only [Sum.inr.injEq] at hdecode
    subst coordinate
    apply Fin.ext
    simp [rightLiteralSlot]
    omega

private theorem mem_deltaLiteralActive_left
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ)
    (coordinate : Fin population) :
    leftLiteralSlot coordinate ∈
        deltaLiteralActive active label seed level ↔
      coordinate ∈ active ∧
        toeplitzHash (label coordinate) seed ∈
          siblingPrefixCell rank level := by
  constructor
  · intro hmember
    rcases Finset.mem_union.mp hmember with hleft | hright
    · rcases Finset.mem_image.mp hleft with
        ⟨source, hsource, hequal⟩
      have hsourceEq : source = coordinate :=
        leftLiteralSlot_injective hequal
      subst source
      exact
        ⟨(Finset.mem_inter.mp hsource).1,
          (mem_hashIndexCell _ _ _ _).mp
            (Finset.mem_inter.mp hsource).2⟩
    · rcases Finset.mem_image.mp hright with
        ⟨source, _hsource, hequal⟩
      exact False.elim
        (left_rightLiteralSlot_ne coordinate source hequal.symm)
  · rintro ⟨hactive, hhash⟩
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact
      ⟨coordinate,
        Finset.mem_inter.mpr
          ⟨hactive, (mem_hashIndexCell _ _ _ _).mpr hhash⟩,
        rfl⟩

private theorem mem_deltaLiteralActive_right
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ)
    (coordinate : Fin population) :
    rightLiteralSlot coordinate ∈
        deltaLiteralActive active label seed level ↔
      toeplitzHash (label coordinate) seed ∈
          zeroPrefixCell rank (level + 1) ∧
        coordinate ∉ active := by
  constructor
  · intro hmember
    rcases Finset.mem_union.mp hmember with hleft | hright
    · rcases Finset.mem_image.mp hleft with
        ⟨source, _hsource, hequal⟩
      exact False.elim
        (left_rightLiteralSlot_ne source coordinate hequal)
    · rcases Finset.mem_image.mp hright with
        ⟨source, hsource, hequal⟩
      have hsourceEq : source = coordinate :=
        rightLiteralSlot_injective hequal
      subst source
      exact
        ⟨(mem_hashIndexCell _ _ _ _).mp
            (Finset.mem_sdiff.mp hsource).1,
          (Finset.mem_sdiff.mp hsource).2⟩
  · rintro ⟨hhash, hactive⟩
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact
      ⟨coordinate,
        Finset.mem_sdiff.mpr
          ⟨(mem_hashIndexCell _ _ _ _).mpr hhash, hactive⟩,
        rfl⟩

/-- Total assignment decoder for the occurrence-variable ABI.  Invalid codes
are false, matching `decodeListLiteralVariable`'s malformed-code semantics. -/
def encodedFiniteBooleanAssignment
    {population : ℕ} (active : Fin population → Bool)
    (code : ℕ) : Bool :=
  if hcode : code < population then active ⟨code, hcode⟩ else false

/-- One masked residual coordinate as a structural polynomial. -/
def structuralMaskedCoordinate
    {population : ℕ} (mask : Finset (Fin population))
    (coordinate : Fin population) : StructuralGF2Polynomial :=
  if coordinate ∈ mask then
    structuralGF2Variable coordinate.val
  else
    structuralGF2Zero

@[simp] theorem evaluateStructuralMaskedCoordinate
    {population : ℕ} (active : Fin population → Bool)
    (mask : Finset (Fin population)) (coordinate : Fin population) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralMaskedCoordinate mask coordinate) =
      (active coordinate && decide (coordinate ∈ mask)) := by
  by_cases hmask : coordinate ∈ mask
  · simp [structuralMaskedCoordinate, hmask,
      encodedFiniteBooleanAssignment, coordinate.isLt]
  · simp [structuralMaskedCoordinate, hmask]

/-- Seed-local list literals lowered into the single shared population of
masked residual variables.  Hash membership is compile-time data; the only
nonconstant atoms are `x` and `1 + x`. -/
def structuralListLiteralAtom
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    StructuralGF2Polynomial :=
  match decodeListLiteralVariable depth population code with
  | none => structuralGF2Zero
  | some (.terminal coordinate) =>
      if toeplitzHash (label coordinate) seed ∈
          zeroPrefixCell rank depth then
        structuralMaskedCoordinate mask coordinate
      else
        structuralGF2Zero
  | some (.delta level slot) =>
      match decodeListLiteralSlot slot with
      | .inl coordinate =>
          if toeplitzHash (label coordinate) seed ∈
              siblingPrefixCell rank level.val then
            structuralMaskedCoordinate mask coordinate
          else
            structuralGF2Zero
      | .inr coordinate =>
          if toeplitzHash (label coordinate) seed ∈
              zeroPrefixCell rank (level.val + 1) then
            structuralGF2Not
              (structuralMaskedCoordinate mask coordinate)
          else
            structuralGF2Zero

/-- Every lowered atom evaluates exactly as the original set-based list
literal on the masked active set. -/
theorem evaluateStructuralListLiteralAtom
    {rank depth population : ℕ}
    (active : Fin population → Bool)
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (code : ℕ) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralListLiteralAtom (depth := depth)
          mask label seed code) =
      match decodeListLiteralVariable depth population code with
      | some literal =>
          listLiteralBooleanAssignment
            ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
            label seed literal
      | none => false := by
  cases hdecode :
      decodeListLiteralVariable depth population code with
  | none =>
      simp [structuralListLiteralAtom, hdecode]
  | some literal =>
    cases literal with
    | terminal coordinate =>
        simp only [structuralListLiteralAtom, hdecode]
        unfold listLiteralBooleanAssignment terminalLiteralActive
        by_cases hhash :
            toeplitzHash (label coordinate) seed ∈
              zeroPrefixCell rank depth
        <;> cases hactive : active coordinate
        <;> by_cases hmask : coordinate ∈ mask
        <;> simp [hhash, hactive, hmask, mem_hashIndexCell]
    | delta level slot =>
        cases hslot : decodeListLiteralSlot slot with
        | inl coordinate =>
          have hslotEq :=
            decodeListLiteralSlot_inl hslot
          subst slot
          simp only [structuralListLiteralAtom, hdecode,
            decodeListLiteralSlot_left]
          change
            evaluateStructuralGF2
                (encodedFiniteBooleanAssignment active)
                (if toeplitzHash (label coordinate) seed ∈
                    siblingPrefixCell rank level.val then
                  structuralMaskedCoordinate mask coordinate
                else structuralGF2Zero) =
              decide
                (leftLiteralSlot coordinate ∈
                  deltaLiteralActive
                    ((Finset.univ.filter fun candidate =>
                      active candidate) ∩ mask)
                    label seed level.val)
          simp only [mem_deltaLiteralActive_left]
          by_cases hhash :
              toeplitzHash (label coordinate) seed ∈
                siblingPrefixCell rank level.val
          <;> cases hactive : active coordinate
          <;> by_cases hmask : coordinate ∈ mask
          <;> simp [hhash, hactive, hmask]
        | inr coordinate =>
          have hslotEq :=
            decodeListLiteralSlot_inr hslot
          subst slot
          simp only [structuralListLiteralAtom, hdecode,
            decodeListLiteralSlot_right]
          change
            evaluateStructuralGF2
                (encodedFiniteBooleanAssignment active)
                (if toeplitzHash (label coordinate) seed ∈
                    zeroPrefixCell rank (level.val + 1) then
                  structuralGF2Not
                    (structuralMaskedCoordinate mask coordinate)
                else structuralGF2Zero) =
              decide
                (rightLiteralSlot coordinate ∈
                  deltaLiteralActive
                    ((Finset.univ.filter fun candidate =>
                      active candidate) ∩ mask)
                    label seed level.val)
          simp only [mem_deltaLiteralActive_right]
          by_cases hhash :
              toeplitzHash (label coordinate) seed ∈
                zeroPrefixCell rank (level.val + 1)
          <;> cases hactive : active coordinate
          <;> by_cases hmask : coordinate ∈ mask
          <;> simp [hhash, hactive, hmask]

/-- One structural list coordinate after lowering all seed-local literals to
the shared masked population. -/
def structuralMaskedListCoordinate
    {rank depth population : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
  StructuralGF2Polynomial :=
  structuralGF2Substitute
    (structuralListLiteralAtom (depth := depth) mask label seed)
    (structuralListPolynomialVector label seed window
      terminalWindow candidate)

def evaluateStructuralListCoordinate
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) : Bool :=
  evaluateStructuralGF2
    (encodedListLiteralBooleanAssignment (depth := depth) active label seed)
    (structuralListPolynomialVector label seed window
      terminalWindow candidate)

theorem evaluateStructuralListCoordinate_eq_compiled
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    evaluateStructuralListCoordinate active label seed window
        terminalWindow candidate =
      compiledListCoordinate active label seed window
        terminalWindow candidate := by
  unfold evaluateStructuralListCoordinate
  change
    evaluateStructuralGF2
        (fun code =>
          match decodeListLiteralVariable depth population code with
          | some literal =>
              listLiteralBooleanAssignment active label seed literal
          | none => false)
        (structuralListPolynomialVector label seed window
          terminalWindow candidate) =
      compiledListCoordinate active label seed window
        terminalWindow candidate
  rw [evaluateStructuralGF2_eq_aeval,
    interpretStructuralListPolynomialVector]
  unfold compiledListCoordinate
  rw [exactPolynomialValue_compiled]

@[simp] theorem evaluateStructuralMaskedListCoordinate
    {rank depth population : ℕ}
    (active : Fin population → Bool)
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralMaskedListCoordinate mask label seed window
          terminalWindow candidate) =
      compiledListCoordinate
        ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
        label seed window terminalWindow candidate := by
  rw [structuralMaskedListCoordinate,
    evaluateStructuralGF2_substitute]
  simp_rw [evaluateStructuralListLiteralAtom]
  exact evaluateStructuralListCoordinate_eq_compiled
    ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
    label seed window terminalWindow candidate

/-- One powered-walk list coordinate as a polynomial in the shared masked
population.  Only the logarithmic walk-time combiner uses the truth-table
compiler; each seed coordinate retains the structural window polynomial. -/
def structuralMaskedWalkListCoordinate
    {rank depth population t : ℕ}
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    StructuralGF2Polynomial :=
  structuralGF2BitMajority fun time =>
    structuralMaskedListCoordinate mask label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate

def executableWalkListCoordinate
    {rank depth population t : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) : Bool :=
  compiledBitMajority fun time =>
    evaluateStructuralListCoordinate active label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate

theorem executableWalkListCoordinate_eq_compiled
    {rank depth population t : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    executableWalkListCoordinate active label window terminalWindow
        sample candidate =
      compiledWalkListCoordinate active label window terminalWindow
        sample candidate := by
  unfold executableWalkListCoordinate compiledWalkListCoordinate
  congr 1
  funext time
  exact evaluateStructuralListCoordinate_eq_compiled active label
    (toeplitzWalkEncoding rank (sample.vertex time)).1
    window terminalWindow candidate

@[simp] theorem evaluateStructuralMaskedWalkListCoordinate
    {rank depth population t : ℕ}
    (active : Fin population → Bool)
    (mask : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment active)
        (structuralMaskedWalkListCoordinate mask label window
          terminalWindow sample candidate) =
      executableWalkListCoordinate
        ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
        label window terminalWindow sample candidate := by
  rw [structuralMaskedWalkListCoordinate,
    evaluateStructuralGF2_bitMajority]
  unfold executableWalkListCoordinate
  congr 1
  funext time
  exact
    (evaluateStructuralMaskedListCoordinate active mask label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate).trans
      (evaluateStructuralListCoordinate_eq_compiled
        ((Finset.univ.filter fun coordinate => active coordinate) ∩ mask)
        label (toeplitzWalkEncoding rank (sample.vertex time)).1
        window terminalWindow candidate).symm

/-- The production occurrence-list coordinate.  The real-valued graded schedule
is absent from execution: `executableGradedWindow` is the proved-equal natural
ceiling formula, and every polynomial is the structural GF(2) syntax above. -/
def executableCanonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) : Bool :=
  executableWalkListCoordinate
    (depth := canonicalGradedDepth
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    active.1
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (executableGradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    gradedTerminalWindow sample candidate

theorem executableCanonicalOccurrenceListCoordinate_refines
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    executableCanonicalOccurrenceListCoordinate occurrences liveScale
        denominator active sample candidate =
      canonicalOccurrenceListCoordinate occurrences liveScale
        denominator active sample candidate := by
  unfold executableCanonicalOccurrenceListCoordinate
    canonicalOccurrenceListCoordinate
  have hwindow :
      executableGradedWindow
          (depth := canonicalGradedDepth
            (touchingCost (occurrenceSupport occurrences)
              (normalizedLiveSet occurrences liveScale)))
          (touchingCost (occurrenceSupport occurrences)
            (normalizedLiveSet occurrences liveScale)) =
        gradedWindow
          (depth := canonicalGradedDepth
            (touchingCost (occurrenceSupport occurrences)
              (normalizedLiveSet occurrences liveScale)))
          (touchingCost (occurrenceSupport occurrences)
            (normalizedLiveSet occurrences liveScale)) := by
    funext level
    exact executableGradedWindow_eq_gradedWindow _ level
  rw [hwindow]
  exact executableWalkListCoordinate_eq_compiled _ _ _ _
    sample candidate

/-- Canonical occurrence-list coordinate as a structural polynomial in the
shared residual-gate variables.  The mask is explicit because every circuit
segment and coefficient digit reuses the same occurrence universe. -/
def structuralCanonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    StructuralGF2Polynomial :=
  structuralMaskedWalkListCoordinate mask
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (executableGradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    gradedTerminalWindow sample candidate

@[simp] theorem evaluateStructuralCanonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index)
        (structuralCanonicalOccurrenceListCoordinate occurrences
          liveScale denominator mask sample candidate) =
      executableCanonicalOccurrenceListCoordinate occurrences
        liveScale denominator
        (normalizedMaskedResidualActiveSet occurrences
          liveScale input mask)
        sample candidate := by
  unfold structuralCanonicalOccurrenceListCoordinate
    executableCanonicalOccurrenceListCoordinate
  simp [normalizedMaskedResidualActiveSet,
    occurrenceMaskedResidualActiveSet, occurrenceResidualActiveSet]

def executableCanonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) : Bool :=
  oneHotLookupRow lookup fun candidate =>
    executableCanonicalOccurrenceListCoordinate occurrences liveScale
      denominator active sample candidate

theorem executableCanonicalOccurrenceLookupRow_refines
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) :
    executableCanonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample lookup =
      canonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample lookup := by
  unfold executableCanonicalOccurrenceLookupRow
    canonicalOccurrenceLookupRow
  congr 1
  funext candidate
  exact executableCanonicalOccurrenceListCoordinate_refines occurrences
    liveScale denominator active sample candidate

/-- Linear structural lookup over the canonical occurrence-list coordinates. -/
def structuralCanonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) :
    StructuralGF2Polynomial :=
  structuralGF2OneHotLookup lookup fun candidate =>
    structuralCanonicalOccurrenceListCoordinate occurrences
      liveScale denominator mask sample candidate

@[simp] theorem evaluateStructuralCanonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index)
        (structuralCanonicalOccurrenceLookupRow occurrences
          liveScale denominator mask sample lookup) =
      executableCanonicalOccurrenceLookupRow occurrences
        liveScale denominator
        (normalizedMaskedResidualActiveSet occurrences
          liveScale input mask)
        sample lookup := by
  rw [structuralCanonicalOccurrenceLookupRow,
    evaluateStructuralGF2_oneHotLookup]
  unfold executableCanonicalOccurrenceLookupRow
  congr 1
  funext candidate
  exact evaluateStructuralCanonicalOccurrenceListCoordinate
    occurrences liveScale denominator input mask sample candidate

def executableCanonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  executableCanonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator
    (normalizedMaskedResidualActiveSet
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    sample
    (shiftedFiniteLookup
      (occurrenceResidualConstantCount
        (symmetricFourfoldOccurrences request) liveScale input
        (symmetricCircuitMask request circuitIndex))
      (symmetricCircuitTopLookup request circuitIndex))

theorem executableCanonicalSymmetricCircuitRow_refines
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) :
    executableCanonicalSymmetricCircuitRow request liveScale denominator
        input circuitIndex sample =
      canonicalSymmetricCircuitRow request liveScale denominator
        input circuitIndex sample := by
  unfold executableCanonicalSymmetricCircuitRow
    canonicalSymmetricCircuitRow
  exact executableCanonicalOccurrenceLookupRow_refines _ _ _ _ _ _

/-- One symmetric circuit segment with its frozen residual-constant offset
made explicit.  The production column selector supplies this offset; the
polynomial itself contains only shared residual variables. -/
def structuralCanonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : ℕ) :
    StructuralGF2Polynomial :=
  structuralCanonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator
    (symmetricCircuitMask request circuitIndex)
    sample
    (shiftedFiniteLookup constantOffset
      (symmetricCircuitTopLookup request circuitIndex))

@[simp] theorem evaluateStructuralCanonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : ℕ)
    (hoffset :
      constantOffset =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet
              (symmetricFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalSymmetricCircuitRow request liveScale
          denominator circuitIndex sample constantOffset) =
      executableCanonicalSymmetricCircuitRow request liveScale denominator
        input circuitIndex sample := by
  subst constantOffset
  unfold structuralCanonicalSymmetricCircuitRow
    executableCanonicalSymmetricCircuitRow
  exact evaluateStructuralCanonicalOccurrenceLookupRow
    (symmetricFourfoldOccurrences request) liveScale denominator input
    (symmetricCircuitMask request circuitIndex) sample
    (shiftedFiniteLookup
      (occurrenceResidualConstantCount
        (symmetricFourfoldOccurrences request) liveScale input
        (symmetricCircuitMask request circuitIndex))
      (symmetricCircuitTopLookup request circuitIndex))

/-- Complete symmetric row polynomial, parameterized only by the finite vector
of frozen circuit offsets selected by the external column. -/
def structuralCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2FiniteConjunction fun circuitIndex =>
    structuralCanonicalSymmetricCircuitRow request liveScale denominator
      circuitIndex sample (constantOffset circuitIndex)

def executableCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  finiteBoolConjunction fun circuitIndex : Fin request.circuits.length =>
    executableCanonicalSymmetricCircuitRow request liveScale denominator input
      circuitIndex sample

theorem executableCanonicalSymmetricFourfoldRow_refines
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) :
    executableCanonicalSymmetricFourfoldRow request liveScale denominator
        input sample =
      canonicalSymmetricFourfoldRow request liveScale denominator
        input sample := by
  unfold executableCanonicalSymmetricFourfoldRow
    canonicalSymmetricFourfoldRow
  apply finiteBoolConjunction_congr
  intro circuitIndex
  exact executableCanonicalSymmetricCircuitRow_refines request liveScale
    denominator input circuitIndex sample

@[simp] theorem evaluateStructuralCanonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet
              (symmetricFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalSymmetricFourfoldRow request liveScale
          denominator sample constantOffset) =
      executableCanonicalSymmetricFourfoldRow request liveScale denominator
        input sample := by
  rw [structuralCanonicalSymmetricFourfoldRow,
    evaluateStructuralGF2_finiteConjunction]
  unfold executableCanonicalSymmetricFourfoldRow
  apply finiteBoolConjunction_congr
  intro circuitIndex
  exact evaluateStructuralCanonicalSymmetricCircuitRow request liveScale
    denominator input circuitIndex sample (constantOffset circuitIndex)
    (hoffset circuitIndex)

theorem evaluateStructuralCanonicalSymmetricFourfoldRow_eq_canonical
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (constantOffset : Fin request.circuits.length → ℕ)
    (hoffset : ∀ circuitIndex,
      constantOffset circuitIndex =
        occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)) :
    evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable
            (symmetricFourfoldOccurrences request)
            (normalizedLiveSet
              (symmetricFourfoldOccurrences request) liveScale)
            input index)
        (structuralCanonicalSymmetricFourfoldRow request liveScale
          denominator sample constantOffset) =
      canonicalSymmetricFourfoldRow request liveScale denominator
        input sample := by
  exact
    (evaluateStructuralCanonicalSymmetricFourfoldRow request liveScale
      denominator input sample constantOffset hoffset).trans
      (executableCanonicalSymmetricFourfoldRow_refines request liveScale
        denominator input sample)

/-- Structural form of the total modular-radix row.  `finFunctionFinEquiv` is
the executable mixed-radix enumeration of all digit tuples; the polynomial
keeps one selected list coordinate per digit and parity across tuple rows. -/
def structuralGF2ModularRadixRow
    {digits populationBound : ℕ}
    (modulus offset base : ℕ)
    (oneHot :
      Fin digits → Fin (populationBound + 1) →
        StructuralGF2Polynomial) :
    StructuralGF2Polynomial :=
  structuralGF2FinParity fun code :
      Fin ((populationBound + 1) ^ digits) =>
    let tuple :=
      (finFunctionFinEquiv :
        (Fin digits → Fin (populationBound + 1)) ≃
          Fin ((populationBound + 1) ^ digits)).symm code
    if modularTupleAccepts modulus offset base tuple then
      structuralGF2FiniteConjunction fun digit =>
        oneHot digit (tuple digit)
    else
      structuralGF2Zero

/-- Canonical modular-radix polynomial over a digit-indexed mask family. -/
def structuralCanonicalOccurrenceModularRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Fin digits → Finset (Fin occurrences.length))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) :
    StructuralGF2Polynomial :=
  structuralGF2ModularRadixRow modulus offset base fun digit candidate =>
    structuralCanonicalOccurrenceListCoordinate occurrences
      liveScale denominator (mask digit) sample candidate

/-- Coefficient-bit specialization of the structural modular-radix row. -/
def structuralCanonicalOccurrenceCoefficientRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) :
    StructuralGF2Polynomial :=
  structuralCanonicalOccurrenceModularRadixRow (digits := digits) occurrences
    liveScale denominator
    (fun digit =>
      mask.filter fun index =>
        (coefficient index).testBit digit.val)
    sample modulus offset 2

/-! ## Residual variables to imported exact equations -/

/-! ## One five-field row ABI -/

/-! ## Fixed public-ABI decoder -/

/-! ## Reusable binary machine arithmetic -/

/-! ## Total canonical finite-index decoders -/

/-! ## Canonical dependent child selections -/

/-! ## Canonical typed-envelope decoding -/

/-! ## One pure total row evaluator -/

/-- Low-to-high interpretation of the row ABI's input field.  The public call
builder always supplies an in-range canonical `encodeBitInput`; defining this
for every natural keeps malformed raw calls total. -/
def rowBitInputOfCode (q code : ℕ) : BitInput q :=
  fun bit => code.testBit bit.val

@[simp] theorem rowBitInputOfCode_encode
    {q : ℕ} (input : BitInput q) :
    rowBitInputOfCode q (encodeBitInput input) = input := by
  funext bit
  unfold rowBitInputOfCode
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt input bit.val bit.isLt

/-! ## Executable rows at the aggregation boundary -/

end NearCubicWires.CanonicalFourfoldRowProgram
