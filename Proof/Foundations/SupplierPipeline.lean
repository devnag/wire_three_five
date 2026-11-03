import Proof.Foundations.CanonicalBinary
import Proof.Foundations.CompilerSemantics
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.CanonicalEncodedListLengthProgram
import Proof.Foundations.ExecutableProgramTightRefuterSource
import Proof.Foundations.OperationalWilliamsSourceCore
import Proof.Foundations.TseitinCNF
import Proof.Foundations.VerifiedLinker
import Mathlib
import Proof.Foundations.Semantics
import Proof.Foundations.ThresholdCompiler

/-!
# Constructive supplier pipeline

This module formalizes the representation and finite-composition layer used by
the Appendix A/B suppliers.  It deliberately stops at three explicit,
lower-level certificates: exact batch printing, a prime surrogate, and
pointwise list amplification.  The source contracts currently state the
ingredients from which those certificates must be built, but do not yet expose
the executable data or the mixing/counting theorems needed to construct them.

Nothing in this file assumes either headline theorem or a circuit lower bound.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierPipeline

open NearCubicWires.CanonicalBinary
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdCompiler

/-! ## Support-first normalization -/

/-- Set all coefficients outside an already-retained physical support to zero.
The threshold is unchanged. -/
def deleteOutsideSupport {n : ℕ} (support : Finset (Fin n))
    (gate : NormalizedThresholdGate n) : NormalizedThresholdGate n where
  weight index := if index ∈ support then gate.weight index else 0
  threshold := gate.threshold

theorem deleteOutsideSupport_zero {n : ℕ} (support : Finset (Fin n))
    (gate : NormalizedThresholdGate n) {index : Fin n}
    (hindex : index ∉ support) :
    (deleteOutsideSupport support gate).weight index = 0 := by
  simp [deleteOutsideSupport, hindex]

/-- Fixing every coordinate outside `support` to false. -/
def restrictToSupport {n : ℕ} (support : Finset (Fin n))
    (input : BitInput n) : BitInput n :=
  fun index => if index ∈ support then input index else false

theorem realGate_restrictToSupport {n : ℕ} (gate : RealThresholdGate n)
    (input : BitInput n) :
    gate.eval (restrictToSupport gate.support input) = gate.eval input := by
  classical
  unfold RealThresholdGate.eval
  apply decide_eq_decide.mpr
  have hsum :
      (∑ index, gate.weight index *
          bitAsReal (restrictToSupport gate.support input index)) =
        ∑ index, gate.weight index * bitAsReal (input index) := by
    apply Finset.sum_congr rfl
    intro index _
    by_cases hindex : index ∈ gate.support
    · simp [restrictToSupport, hindex]
    · have hweight : gate.weight index = 0 := by
        by_contra hnonzero
        exact hindex ((gate.mem_support_iff index).2 hnonzero)
      simp [restrictToSupport, hindex, hweight]
  rw [hsum]

theorem deleteOutsideSupport_eval {n : ℕ} (support : Finset (Fin n))
    (gate : NormalizedThresholdGate n) (input : BitInput n) :
    (deleteOutsideSupport support gate).eval input =
      gate.eval (restrictToSupport support input) := by
  classical
  unfold NormalizedThresholdGate.eval
  apply decide_eq_decide.mpr
  have hsum :
      (∑ index, (deleteOutsideSupport support gate).weight index *
          if input index then 1 else 0) =
        ∑ index, gate.weight index *
          if restrictToSupport support input index then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro index _
    by_cases hindex : index ∈ support
    · simp [deleteOutsideSupport, restrictToSupport, hindex]
    · simp [deleteOutsideSupport, restrictToSupport, hindex]
  simpa [deleteOutsideSupport] using congrArg (fun score => gate.threshold ≤ score) hsum

theorem deleteOutsideSupport_parameters {n bound : ℕ}
    (support : Finset (Fin n)) (gate : NormalizedThresholdGate n)
    (hbound : gate.parametersBoundedBy bound) :
    (deleteOutsideSupport support gate).parametersBoundedBy bound := by
  constructor
  · intro index
    by_cases hindex : index ∈ support
    · simpa [deleteOutsideSupport, hindex] using hbound.1 index
    · simp [deleteOutsideSupport, hindex]
  · simpa [deleteOutsideSupport] using hbound.2

/-- Integer syntax paired with the exact support charged by the physical
circuit.  `zeroOutside` prevents the charged support and the semantics from
drifting apart. -/
structure SupportedNormalizedGate (n : ℕ) where
  gate : NormalizedThresholdGate n
  support : Finset (Fin n)
  zeroOutside : ∀ index, index ∉ support → gate.weight index = 0

def SupportedNormalizedGate.eval {n : ℕ} (gate : SupportedNormalizedGate n)
    (input : BitInput n) : Bool :=
  gate.gate.eval input

def SupportedNormalizedGate.wireCount {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  gate.support.card

/-- The imported cube-normalization theorem can be made support preserving:
evaluate its representation only on the source's retained coordinates and
delete all other coefficients. -/
theorem normalizeGatePreservingSupportPositive
    (normalization : ThresholdNormalizationContract)
    {n : ℕ} (hn : 0 < n) (source : RealThresholdGate n) :
    ∃ target : SupportedNormalizedGate n,
      (∀ input, target.eval input = source.eval input) ∧
      target.support = source.support ∧
      target.gate.parametersBoundedBy (n ^ n) := by
  rcases normalization n hn source with ⟨raw, hrawEval, hrawBound⟩
  let deleted := deleteOutsideSupport source.support raw
  refine ⟨{
    gate := deleted
    support := source.support
    zeroOutside := ?_
  }, ?_, rfl, deleteOutsideSupport_parameters _ _ hrawBound⟩
  · intro index hindex
    exact deleteOutsideSupport_zero source.support raw hindex
  · intro input
    change deleted.eval input = source.eval input
    rw [show deleted.eval input =
      raw.eval (restrictToSupport source.support input) by
        exact deleteOutsideSupport_eval source.support raw input]
    rw [hrawEval]
    exact realGate_restrictToSupport source input

/-- The zero-arity case is a constant gate and needs no imported
normalization algorithm. -/
noncomputable def normalizeZeroArityGate
    (source : RealThresholdGate 0) : SupportedNormalizedGate 0 where
  gate :=
    { weight := fun index => Fin.elim0 index
      threshold :=
        if source.eval (fun index => Fin.elim0 index) then 0 else 1 }
  support := source.support
  zeroOutside := fun index => Fin.elim0 index

theorem normalizeZeroArityGate_eval
    (source : RealThresholdGate 0) (input : BitInput 0) :
    (normalizeZeroArityGate source).eval input = source.eval input := by
  have hinput : input = (fun index => Fin.elim0 index) :=
    Subsingleton.elim _ _
  subst input
  cases hvalue : source.eval (fun index => Fin.elim0 index) <;>
    simp [normalizeZeroArityGate, SupportedNormalizedGate.eval,
      NormalizedThresholdGate.eval, hvalue]

theorem normalizeZeroArityGate_parameters (source : RealThresholdGate 0) :
    (normalizeZeroArityGate source).gate.parametersBoundedBy (0 ^ 0) := by
  constructor
  · intro index
    exact Fin.elim0 index
  · cases hvalue : source.eval (fun index => Fin.elim0 index) <;>
      simp [normalizeZeroArityGate, hvalue]

/-- Total support-first normalization, including constant zero-arity gates. -/
theorem normalizeGatePreservingSupport
    (normalization : ThresholdNormalizationContract)
    {n : ℕ} (source : RealThresholdGate n) :
    ∃ target : SupportedNormalizedGate n,
      (∀ input, target.eval input = source.eval input) ∧
      target.support = source.support ∧
      target.gate.parametersBoundedBy (n ^ n) := by
  by_cases hn : 0 < n
  · exact normalizeGatePreservingSupportPositive normalization hn source
  · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact ⟨normalizeZeroArityGate source,
      normalizeZeroArityGate_eval source, rfl,
      normalizeZeroArityGate_parameters source⟩

/-! ## Exact live/frozen residualization -/

def liveScore {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) : ℤ :=
  ∑ index ∈ live, gate.weight index * bitInt (input index)

def frozenScore {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) : ℤ :=
  ∑ index ∈ Finset.univ \ live,
    gate.weight index * bitInt (input index)

def minimumLiveScore {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) : ℤ :=
  ∑ index ∈ live, if gate.weight index < 0 then gate.weight index else 0

theorem normalizedScore_split {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n) :
    (∑ index, gate.weight index * bitInt (input index)) =
      liveScore gate live input + frozenScore gate live input := by
  classical
  unfold liveScore frozenScore
  let score : Fin n → ℤ :=
    fun index => gate.weight index * bitInt (input index)
  change Finset.sum Finset.univ score =
    Finset.sum live score + Finset.sum (Finset.univ \ live) score
  calc
    Finset.sum Finset.univ score =
        Finset.sum (live ∪ (Finset.univ \ live)) score := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ live)]
    _ = Finset.sum live score +
        Finset.sum (Finset.univ \ live) score :=
      Finset.sum_union Finset.disjoint_sdiff

theorem minimumLiveScore_le {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n) :
    minimumLiveScore gate live ≤ liveScore gate live input := by
  unfold minimumLiveScore liveScore
  apply Finset.sum_le_sum
  intro index hindex
  by_cases hnegative : gate.weight index < 0
  · rw [if_pos hnegative]
    cases input index
    · simpa only [bitInt_eq_toNat, Bool.toNat_false,
        CharP.cast_eq_zero, mul_zero] using le_of_lt hnegative
    · simp only [bitInt_eq_toNat, Bool.toNat_true, Nat.cast_one, mul_one]
      exact le_rfl
  · rw [if_neg hnegative]
    cases input index
    · simp only [bitInt_eq_toNat, Bool.toNat_false,
        CharP.cast_eq_zero, mul_zero]
      exact le_rfl
    · simpa only [bitInt_eq_toNat, Bool.toNat_true,
        Nat.cast_one, mul_one] using le_of_not_gt hnegative

/-- The frozen-side bit `C` of Appendix A.2. -/
def residualConstant {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) : Bool :=
  decide
    (gate.threshold - minimumLiveScore gate live ≤
      frozenScore gate live input)

/-- The nonconstant residue `Z = X xor C`. -/
def residualVariable {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (input : BitInput n) : Bool :=
  xor (gate.eval input) (residualConstant gate live input)

theorem residualConstant_implies_gate {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n)
    (hconstant : residualConstant gate live input = true) :
    gate.eval input = true := by
  have hfrozen :
      gate.threshold - minimumLiveScore gate live ≤
        frozenScore gate live input := by
    exact of_decide_eq_true hconstant
  have hlive := minimumLiveScore_le gate live input
  have hscore :
      gate.threshold ≤
        liveScore gate live input + frozenScore gate live input := by
    omega
  unfold NormalizedThresholdGate.eval
  apply decide_eq_true
  rw [normalizedScore_eq_bitInt]
  rwa [normalizedScore_split]

/-- Integer form used by population lookups: `C` and `Z` are never
simultaneously one, so Boolean xor is ordinary addition at this boundary. -/
theorem residual_sum_reconstruction {n : ℕ}
    (gate : NormalizedThresholdGate n) (live : Finset (Fin n))
    (input : BitInput n) :
    (residualConstant gate live input).toNat +
        (residualVariable gate live input).toNat =
      (gate.eval input).toNat := by
  unfold residualVariable
  cases hgate : gate.eval input <;>
    cases hconstant : residualConstant gate live input
  · rfl
  · exact False.elim (by
      have := residualConstant_implies_gate gate live input hconstant
      simp [hgate] at this)
  · rfl
  · rfl

/-! ## Concrete normalized circuit families -/

structure NormalizedSymmetricThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → SupportedNormalizedGate n
  top : Fin (bottomCount + 1) → Bool

def NormalizedSymmetricThresholdCircuit.acceptedBottomCount {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (input : BitInput n) : Fin (circuit.bottomCount + 1) :=
  ⟨(Finset.univ.filter fun i => (circuit.bottom i).eval input).card, by
    apply Nat.lt_succ_of_le
    simpa using Finset.card_le_card (Finset.filter_subset
      (fun i => (circuit.bottom i).eval input) Finset.univ)⟩

def NormalizedSymmetricThresholdCircuit.eval {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (input : BitInput n) : Bool :=
  circuit.top (circuit.acceptedBottomCount input)

def NormalizedSymmetricThresholdCircuit.wireCount {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) : ℕ :=
  ∑ i, ((circuit.bottom i).wireCount + 1)

structure NormalizedThresholdThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → SupportedNormalizedGate n
  top : SupportedNormalizedGate bottomCount

def NormalizedThresholdThresholdCircuit.bottomValues {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) : BitInput circuit.bottomCount :=
  fun index => (circuit.bottom index).eval input

def NormalizedThresholdThresholdCircuit.eval {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) : Bool :=
  circuit.top.eval (circuit.bottomValues input)

/-- Only retained top occurrences charge bottom gates. -/
def NormalizedThresholdThresholdCircuit.wireCount {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) : ℕ :=
  ∑ i ∈ circuit.top.support, ((circuit.bottom i).wireCount + 1)

theorem normalizeSymmetricCircuit
    (normalization : ThresholdNormalizationContract)
    {n : ℕ} (source : SymmetricThresholdCircuit n) :
    ∃ target : NormalizedSymmetricThresholdCircuit n,
      (∀ input, target.eval input = source.eval input) ∧
      target.wireCount = source.wireCount ∧
      ∀ index, (target.bottom index).gate.parametersBoundedBy (n ^ n) := by
  classical
  have hbottom : ∀ index : Fin source.bottomCount,
      ∃ target : SupportedNormalizedGate n,
        (∀ input, target.eval input = (source.bottom index).eval input) ∧
        target.support = (source.bottom index).support ∧
        target.gate.parametersBoundedBy (n ^ n) :=
    fun index => normalizeGatePreservingSupport normalization (source.bottom index)
  let bottom : Fin source.bottomCount → SupportedNormalizedGate n :=
    fun index => Classical.choose (hbottom index)
  have hsemantics (index : Fin source.bottomCount) (input : BitInput n) :
      (bottom index).eval input = (source.bottom index).eval input :=
    (Classical.choose_spec (hbottom index)).1 input
  have hsupport (index : Fin source.bottomCount) :
      (bottom index).support = (source.bottom index).support :=
    (Classical.choose_spec (hbottom index)).2.1
  let target : NormalizedSymmetricThresholdCircuit n := {
    bottomCount := source.bottomCount
    bottom := bottom
    top := fun count => source.top count.val
  }
  refine ⟨target, ?_, ?_, ?_⟩
  · intro input
    have hfilter :
        (Finset.univ.filter fun i => (bottom i).eval input) =
          Finset.univ.filter fun i => (source.bottom i).eval input := by
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hsemantics index input]
    simp only [NormalizedSymmetricThresholdCircuit.eval,
      NormalizedSymmetricThresholdCircuit.acceptedBottomCount,
      SymmetricThresholdCircuit.eval, target]
    change source.top
        ((Finset.univ.filter fun i => (bottom i).eval input).card) =
      source.top
        ((Finset.univ.filter fun i => (source.bottom i).eval input).card)
    rw [hfilter]
  · unfold NormalizedSymmetricThresholdCircuit.wireCount
    unfold SymmetricThresholdCircuit.wireCount
    dsimp [target]
    refine Finset.sum_congr rfl ?_
    intro index _
    simp only [SupportedNormalizedGate.wireCount]
    rw [hsupport index]
  · intro index
    dsimp [target]
    exact (Classical.choose_spec (hbottom index)).2.2

/-- The real top gate represented by a concrete `THR ∘ THR` circuit. -/
noncomputable def realTopGate {n : ℕ} (source : ThresholdThresholdCircuit n) :
    RealThresholdGate source.bottomCount where
  weight := source.topWeight
  threshold := source.topThreshold
  support := Finset.univ.filter fun index => source.topWeight index ≠ 0
  mem_support_iff := by simp

theorem normalizeThresholdCircuit
    (normalization : ThresholdNormalizationContract)
    {n : ℕ} (source : ThresholdThresholdCircuit n) :
    ∃ target : NormalizedThresholdThresholdCircuit n,
      (∀ input, target.eval input = source.eval input) ∧
      target.wireCount = source.wireCount ∧
      target.bottomCount = source.bottomCount ∧
      (∀ index, (target.bottom index).gate.parametersBoundedBy (n ^ n)) ∧
      target.top.gate.parametersBoundedBy
        (source.bottomCount ^ source.bottomCount) := by
  classical
  have hbottom : ∀ index : Fin source.bottomCount,
      ∃ target : SupportedNormalizedGate n,
        (∀ input, target.eval input = (source.bottom index).eval input) ∧
        target.support = (source.bottom index).support ∧
        target.gate.parametersBoundedBy (n ^ n) :=
    fun index => normalizeGatePreservingSupport normalization (source.bottom index)
  let bottom : Fin source.bottomCount → SupportedNormalizedGate n :=
    fun index => Classical.choose (hbottom index)
  have hbottomEval (index : Fin source.bottomCount) (input : BitInput n) :
      (bottom index).eval input = (source.bottom index).eval input :=
    (Classical.choose_spec (hbottom index)).1 input
  have hbottomSupport (index : Fin source.bottomCount) :
      (bottom index).support = (source.bottom index).support :=
    (Classical.choose_spec (hbottom index)).2.1
  rcases normalizeGatePreservingSupport normalization (realTopGate source) with
    ⟨top, htopEval, htopSupport, htopBound⟩
  let target : NormalizedThresholdThresholdCircuit n := {
    bottomCount := source.bottomCount
    bottom := bottom
    top := top
  }
  refine ⟨target, ?_, ?_, rfl, ?_, htopBound⟩
  · intro input
    dsimp [target]
    unfold NormalizedThresholdThresholdCircuit.eval
    rw [htopEval]
    unfold ThresholdThresholdCircuit.eval
    apply decide_eq_decide.mpr
    have hsum :
        (∑ index, source.topWeight index *
          bitAsReal ((bottom index).eval input)) =
        ∑ index, source.topWeight index *
          bitAsReal ((source.bottom index).eval input) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hbottomEval index input]
    simpa [realTopGate, NormalizedThresholdThresholdCircuit.bottomValues] using
      congrArg (fun score => source.topThreshold ≤ score) hsum
  · unfold NormalizedThresholdThresholdCircuit.wireCount
    unfold ThresholdThresholdCircuit.wireCount
    dsimp [target]
    rw [htopSupport]
    rw [show (realTopGate source).support =
      Finset.univ.filter (fun index => source.topWeight index ≠ 0) by rfl]
    refine Finset.sum_congr rfl ?_
    intro index _
    simp only [SupportedNormalizedGate.wireCount]
    rw [hbottomSupport index]
  · intro index
    dsimp [target]
    exact (Classical.choose_spec (hbottom index)).2.2

/-! ## Executable disjoint top children -/

def conjunctionBit {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (circuits : List Circuit) (input : BitInput q) : Bool :=
  circuits.all fun circuit => evaluate circuit input

theorem conjunctionBit_toNat {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (circuits : List Circuit) (input : BitInput q) :
    (conjunctionBit evaluate circuits input).toNat =
      (circuits.map fun circuit => (evaluate circuit input).toNat).prod := by
  induction circuits with
  | nil =>
      rfl
  | cons circuit circuits inductionHypothesis =>
      change
        (evaluate circuit input &&
          conjunctionBit evaluate circuits input).toNat =
        (evaluate circuit input).toNat *
          (circuits.map fun candidate => (evaluate candidate input).toNat).prod
      rw [← inductionHypothesis]
      cases evaluate circuit input <;>
        cases conjunctionBit evaluate circuits input <;>
        rfl

/-- Canonical sorted coordinate map for the top gate's physically retained
bottom inputs. -/
def retainedTopIndex {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) :
    Fin circuit.top.support.card ↪o Fin circuit.bottomCount :=
  circuit.top.support.orderEmbOfFin rfl

/-- Support-compressed top gate.  Decomposing this gate prevents imported
children from introducing coefficients on bottom gates that the circuit did
not physically retain. -/
def retainedTopGate {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) :
    NormalizedThresholdGate circuit.top.support.card where
  weight index := circuit.top.gate.weight (retainedTopIndex circuit index)
  threshold := circuit.top.gate.threshold

def retainedBottomValues {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) : BitInput circuit.top.support.card :=
  fun index => (circuit.bottom (retainedTopIndex circuit index)).eval input

theorem retainedTopGate_eval {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) :
    (retainedTopGate circuit).eval (retainedBottomValues circuit input) =
      circuit.eval input := by
  have henumerate :
      (∑ index : Fin circuit.top.support.card,
          circuit.top.gate.weight (retainedTopIndex circuit index) *
            bitInt ((circuit.bottom
              (retainedTopIndex circuit index)).eval input)) =
        ∑ index ∈ circuit.top.support,
          circuit.top.gate.weight index *
            bitInt ((circuit.bottom index).eval input) := by
    let embedding : Fin circuit.top.support.card ↪ Fin circuit.bottomCount :=
      (retainedTopIndex circuit).toEmbedding
    have hmap :
        Finset.map embedding Finset.univ = circuit.top.support := by
      simp [embedding, retainedTopIndex]
    change
      (∑ index : Fin circuit.top.support.card,
          circuit.top.gate.weight (embedding index) *
            bitInt ((circuit.bottom (embedding index)).eval input)) =
        ∑ index ∈ circuit.top.support,
          circuit.top.gate.weight index *
            bitInt ((circuit.bottom index).eval input)
    conv_rhs => rw [← hmap]
    exact (Finset.sum_map Finset.univ embedding
      (fun index =>
        circuit.top.gate.weight index *
          bitInt ((circuit.bottom index).eval input))).symm
  have hsupport :
      (∑ index ∈ circuit.top.support,
          circuit.top.gate.weight index *
            bitInt ((circuit.bottom index).eval input)) =
        ∑ index,
          circuit.top.gate.weight index *
            bitInt ((circuit.bottom index).eval input) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro index _ houtside
    rw [circuit.top.zeroOutside index houtside]
    simp
  unfold retainedTopGate retainedBottomValues
    NormalizedThresholdGate.eval
    NormalizedThresholdThresholdCircuit.eval
    NormalizedThresholdThresholdCircuit.bottomValues
    SupportedNormalizedGate.eval
  apply decide_eq_decide.mpr
  unfold bitInt SupportedNormalizedGate.eval at henumerate hsupport
  rw [henumerate, hsupport]

theorem filterLength_eq_any_toNat
    {Item : Type} (items : List Item) (predicate : Item → Bool)
    (hdisjoint : (items.filter predicate).length ≤ 1) :
    (items.filter predicate).length = (items.any predicate).toNat := by
  induction items with
  | nil =>
      rfl
  | cons item items inductionHypothesis =>
      by_cases hitem : predicate item = true
      · have htailLength : (items.filter predicate).length = 0 := by
          simp only [List.filter_cons, hitem, ↓reduceIte, List.length_cons] at hdisjoint
          omega
        have htailFilter : items.filter predicate = [] :=
          List.length_eq_zero_iff.mp htailLength
        have htailAny : items.any predicate = false := by
          rw [List.any_eq_false]
          intro candidate hcandidate
          cases hcandidateValue : predicate candidate
          · simp
          · have hmem : candidate ∈ items.filter predicate :=
              List.mem_filter.mpr ⟨hcandidate, hcandidateValue⟩
            rw [htailFilter] at hmem
            simp at hmem
        simp [hitem, htailLength, htailAny]
      · have hitemFalse : predicate item = false :=
          Bool.eq_false_of_not_eq_true hitem
        have htailDisjoint : (items.filter predicate).length ≤ 1 := by
          simpa [hitemFalse] using hdisjoint
        simpa [hitemFalse] using inductionHypothesis htailDisjoint

/-! ## Exact mixed-radix stacking -/

structure LabelledEquation (Carrier : Type) where
  weights : Carrier → ℤ
  target : ℤ

def LabelledEquation.score {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (input : Carrier → Bool) : ℤ :=
  ∑ index, equation.weights index * bitInt (input index)

def LabelledEquation.difference {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (input : Carrier → Bool) : ℤ :=
  equation.score input - equation.target

def LabelledEquation.Holds {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (input : Carrier → Bool) : Prop :=
  equation.difference input = 0

def LabelledEquation.HoldsModulo {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (modulus : ℤ)
    (input : Carrier → Bool) : Prop :=
  equation.difference input % modulus = 0

theorem LabelledEquation.holdsModulo_of_holds
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier) (modulus : ℤ)
    (input : Carrier → Bool) (hholds : equation.Holds input) :
    equation.HoldsModulo modulus input := by
  unfold LabelledEquation.Holds at hholds
  change equation.difference input % modulus = 0
  rw [hholds]
  exact trueEquationPassesEveryModulus modulus

/-- Canonical mixed-radix stack for an occurrence list of exact equations.
The empty conjunction is represented by `0 = 0`. -/
def stackEquations {Carrier : Type} (base : ℤ) :
    List (LabelledEquation Carrier) → LabelledEquation Carrier
  | [] =>
      { weights := fun _ => 0
        target := 0 }
  | equation :: equations =>
      let tail := stackEquations base equations
      { weights := fun index =>
          equation.weights index + base * tail.weights index
        target := equation.target + base * tail.target }

@[simp] theorem stackEquations_difference_nil
    {Carrier : Type} [Fintype Carrier] (base : ℤ)
    (input : Carrier → Bool) :
    (stackEquations base []).difference input = 0 := by
  simp [stackEquations, LabelledEquation.difference,
    LabelledEquation.score]

@[simp] theorem stackEquations_difference_cons
    {Carrier : Type} [Fintype Carrier] (base : ℤ)
    (equation : LabelledEquation Carrier)
    (equations : List (LabelledEquation Carrier))
    (input : Carrier → Bool) :
    (stackEquations base (equation :: equations)).difference input =
      equation.difference input +
        base * (stackEquations base equations).difference input := by
  change
    (∑ index,
        (equation.weights index +
          base * (stackEquations base equations).weights index) *
            bitInt (input index)) -
      (equation.target +
        base * (stackEquations base equations).target) =
      (∑ index, equation.weights index * bitInt (input index)) -
          equation.target +
        base *
          ((∑ index, (stackEquations base equations).weights index *
              bitInt (input index)) -
            (stackEquations base equations).target)
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- Bounded mixed-radix digits cannot cancel.  This is the arbitrary-length
version used for exact-equation monomials; duplicates remain distinct list
occurrences. -/
theorem stackEquations_holds_iff {Carrier : Type} [Fintype Carrier]
    (base : ℤ) (equations : List (LabelledEquation Carrier))
    (input : Carrier → Bool) (hbase : 0 < base)
    (hbound : ∀ equation ∈ equations,
      -base < equation.difference input ∧
        equation.difference input < base) :
    (stackEquations base equations).Holds input ↔
      ∀ equation ∈ equations, equation.Holds input := by
  induction equations with
  | nil =>
      simp [stackEquations, LabelledEquation.Holds,
        LabelledEquation.difference, LabelledEquation.score]
  | cons equation equations inductionHypothesis =>
      have hequationBound := hbound equation (by simp)
      have htailBound : ∀ candidate ∈ equations,
          -base < candidate.difference input ∧
            candidate.difference input < base := by
        intro candidate hcandidate
        exact hbound candidate (by simp [hcandidate])
      have htail := inductionHypothesis htailBound
      have hbaseNe : base ≠ 0 := ne_of_gt hbase
      constructor
      · intro hstack
        unfold LabelledEquation.Holds at hstack
        rw [stackEquations_difference_cons] at hstack
        have hdiv : base ∣ equation.difference input := by
          refine ⟨-(stackEquations base equations).difference input, ?_⟩
          linarith
        have hequation :
            equation.difference input = 0 :=
          boundedMultipleIsZero base (equation.difference input)
            hbase hequationBound.1 hequationBound.2 hdiv
        have htailDifference :
            (stackEquations base equations).difference input = 0 := by
          rw [hequation, zero_add] at hstack
          exact (mul_eq_zero.mp hstack).resolve_left hbaseNe
        have htailHolds :
            (stackEquations base equations).Holds input :=
          htailDifference
        have htailEvery := htail.mp htailHolds
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with rfl | hcandidate
        · exact hequation
        · exact htailEvery candidate hcandidate
      · intro hevery
        have hequation :
            equation.difference input = 0 :=
          hevery equation (by simp)
        have htailEvery :
            ∀ candidate ∈ equations, candidate.Holds input := by
          intro candidate hcandidate
          exact hevery candidate (by simp [hcandidate])
        have htailHolds := htail.mpr htailEvery
        unfold LabelledEquation.Holds at htailHolds ⊢
        rw [stackEquations_difference_cons, hequation, htailHolds]
        ring

/-! ## Literal Appendix A supplier propositions -/

abbrev CircuitFamily := ℕ → Type

/-- Family tags are part of every normalized circuit and Fourfold envelope.
The outer tag is essential for empty batches, where there is no circuit code
from which a shared program could infer the mode. -/
def symmetricCircuitFamilyTag : ℕ := 0

def thresholdCircuitFamilyTag : ℕ := 1

/-- A dependent request keeps the arity and its circuit batch inseparable. -/
structure FourfoldRequest (Circuit : CircuitFamily) where
  q : ℕ
  circuits : List (Circuit q)

def batchDescription {Circuit : Type} (description : Circuit → ℕ)
    (circuits : List Circuit) : ℕ :=
  (circuits.map description).sum

/-- Canonical nonnegative-rational decoding.  Both components remain canonical
binary syntax at the executable ABI; no later weak-machine controller has to
recover a native numerator or denominator hidden inside an opaque pair.  The
denominator predecessor keeps zero denominators unrepresentable. -/
def decodeSupplierRational (code : ℕ) : ℚ :=
  let pair := Nat.unpair code
  match decodeNat pair.1, decodeNat pair.2 with
  | some numerator, some denominatorTail =>
      (numerator : ℚ) / (denominatorTail + 1 : ℕ)
  | _, _ => 0

noncomputable def booleanMean {Index : Type} [Fintype Index]
    (value : Index → Bool) : ℝ :=
  (∑ index, bitAsReal (value index)) / Fintype.card Index

noncomputable def conjunctionProbability {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (circuits : List Circuit) : ℝ :=
  booleanMean fun input => conjunctionBit evaluate circuits input

def SupportedNormalizedGate.descriptionBits {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  gate.gate.encodingBits + n

def NormalizedSymmetricThresholdCircuit.descriptionBits {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) : ℕ :=
  circuit.bottomCount + 1 +
    ∑ index, (circuit.bottom index).descriptionBits

def NormalizedThresholdThresholdCircuit.descriptionBits {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) : ℕ :=
  circuit.top.descriptionBits +
    ∑ index, (circuit.bottom index).descriptionBits

def encodeSupportedNormalizedGate {n : ℕ}
    (gate : SupportedNormalizedGate n) : ℕ :=
  encodeTaggedList
    [encodeIntList (List.ofFn gate.gate.weight),
      encodeInt gate.gate.threshold,
      encodeBoolList
        (List.ofFn fun index => decide (index ∈ gate.support))]

def encodeNormalizedSymmetricThresholdCircuit {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) : ℕ :=
  encodeTaggedList
    [encodeNat symmetricCircuitFamilyTag,
      encodeNat circuit.bottomCount,
      encodeBalancedList
        (List.ofFn fun index =>
          encodeSupportedNormalizedGate (circuit.bottom index)),
      encodeBoolList (List.ofFn circuit.top)]

def encodeNormalizedThresholdThresholdCircuit {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) : ℕ :=
  encodeTaggedList
    [encodeNat thresholdCircuitFamilyTag,
      encodeNat circuit.bottomCount,
      encodeBalancedList
        (List.ofFn fun index =>
          encodeSupportedNormalizedGate (circuit.bottom index)),
      encodeSupportedNormalizedGate circuit.top]

/-! ## Finite supplier certificates and their composition -/

/-- A finite prime surrogate for one family of exact equations.  Completeness
and pointwise soundness are the precise obligations that the RS theta bound
and divisor-count argument must discharge. -/
structure PrimeSurrogateCertificate (Equation Prime Input : Type)
    [Fintype Prime] where
  cardPositive : 0 < Fintype.card Prime
  exact : Equation → Input → Bool
  modular : Equation → Prime → Input → Bool
  error : ℝ
  errorNonnegative : 0 ≤ error
  complete : ∀ equation input, exact equation input →
    ∀ prime, modular equation prime input
  sound : ∀ equation input, ¬exact equation input →
    booleanMean (fun prime => modular equation prime input) ≤ error

/-- Pointwise list amplification.  The failure probability is stated for each
input separately; no global seed is assumed. -/
structure AmplifiedListCertificate (Input Seed : Type) [Fintype Seed] where
  cardPositive : 0 < Fintype.card Seed
  succeeds : Input → Seed → Bool
  failure : ℝ
  failureNonnegative : 0 ≤ failure
  pointwise : ∀ input,
    booleanMean (fun seed => !(succeeds input seed)) ≤ failure

theorem booleanMean_le_one {Index : Type} [Fintype Index]
    [Nonempty Index] (value : Index → Bool) :
    booleanMean value ≤ 1 := by
  unfold booleanMean
  have hcard : (0 : ℝ) < Fintype.card Index := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_one hcard).2
  calc
    (∑ index, bitAsReal (value index)) ≤ ∑ _index : Index, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _
      cases value index <;> simp [bitAsReal]
    _ = Fintype.card Index := by simp

theorem sum_pointwise_error
    {Index : Type} [Fintype Index]
    (exact approximate : Index → ℝ) (error : ℝ)
    (herror : ∀ index, |approximate index - exact index| ≤ error) :
    |(∑ index, approximate index) - ∑ index, exact index| ≤
      Fintype.card Index * error := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ index, (approximate index - exact index)| ≤
        ∑ index, |approximate index - exact index| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _index : Index, error :=
      Finset.sum_le_sum fun index _ => herror index
    _ = Fintype.card Index * error := by simp

/-! ## Source-contract consequences available without new assumptions -/

end NearCubicWires.SupplierPipeline
