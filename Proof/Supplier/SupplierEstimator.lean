import Proof.Supplier.BoundedNormalizedSupplier
import Proof.Supplier.SupplierAsymptotics
import Proof.Supplier.SupplierCapacity
import Proof.Foundations.SupplierPrime
import Proof.Foundations.SupplierPrinter
import Proof.Supplier.SupplierRadix
import Proof.Supplier.SupplierTouching
import Proof.Supplier.SupplierWalkBridge
import Proof.Circuits.ThresholdAlignedEnvelope

/-!
# Shared fourfold supplier estimator

The two normalized circuit families use one finite row-aggregation kernel.  This
file keeps the mathematical estimate, its canonical rational output, and the
fixed-program boundary synchronized; the symmetric and threshold modes differ
only in the rows supplied to that kernel.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierEstimator

open NearCubicWires
open NearCubicWires.BoundedNormalizedSupplier
open NearCubicWires.CanonicalBinary
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierAsymptotics
open NearCubicWires.SupplierCapacity
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
open NearCubicWires.SupplierWindow
open NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.ThresholdCompiler

/-! ## Canonical nonnegative rational output -/

/-- Canonical code for `numerator / (denominatorTail + 1)`.  Storing the
denominator predecessor makes zero denominators unrepresentable.  Components
stay as canonical bit-list codes so downstream fixed programs can inspect or
compare them without materializing large native naturals. -/
def encodeNaturalRatio (numerator denominatorTail : ℕ) : ℕ :=
  Nat.pair (encodeNat numerator) (encodeNat denominatorTail)

@[simp] theorem decodeSupplierRational_encodeNaturalRatio
    (numerator denominatorTail : ℕ) :
    decodeSupplierRational (encodeNaturalRatio numerator denominatorTail) =
      (numerator : ℚ) / (denominatorTail + 1 : ℕ) := by
  simp [decodeSupplierRational, encodeNaturalRatio]

/-! ## Shared normalized occurrence preprocessing -/

/-- Retained bottom occurrences of one symmetric circuit, in canonical gate
index order.  Repeated gates remain repeated physical occurrences. -/
def symmetricCircuitOccurrences {q : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit q) :
    List (SupportedNormalizedGate q) :=
  List.ofFn circuit.bottom

/-- Retained bottom occurrences of one threshold-top circuit, in exactly the
sorted support order used by `retainedTopGate`. -/
def thresholdCircuitOccurrences {q : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit q) :
    List (SupportedNormalizedGate q) :=
  List.ofFn fun index : Fin circuit.top.support.card =>
    circuit.bottom (retainedTopIndex circuit index)

def symmetricFourfoldOccurrences
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (SupportedNormalizedGate request.q) :=
  request.circuits.flatMap symmetricCircuitOccurrences

def thresholdFourfoldOccurrences
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    List (SupportedNormalizedGate request.q) :=
  request.circuits.flatMap thresholdCircuitOccurrences

/-- One occurrence-indexed support interface shared by touching, list
generation, and every later row compiler. -/
def occurrenceSupport {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
  (index : Fin occurrences.length) : Finset (Fin q) :=
  (occurrences.get index).support

def occurrenceWireCount {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) : ℕ :=
  (occurrences.map SupportedNormalizedGate.wireCount).sum

theorem supportIncidenceMass_occurrenceSupport {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) :
    supportIncidenceMass (occurrenceSupport occurrences) =
      occurrenceWireCount occurrences := by
  have hlist :
      occurrences.map SupportedNormalizedGate.wireCount =
        List.ofFn (fun index : Fin occurrences.length =>
          (occurrences.get index).wireCount) := by
    simp [List.ofFn_getElem_eq_map]
  unfold supportIncidenceMass occurrenceSupport occurrenceWireCount
  rw [hlist, List.sum_ofFn]
  rfl

theorem symmetricCircuitOccurrences_wireCount {q : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit q) :
    occurrenceWireCount (symmetricCircuitOccurrences circuit) +
        (symmetricCircuitOccurrences circuit).length =
      circuit.wireCount := by
  unfold occurrenceWireCount symmetricCircuitOccurrences
    NormalizedSymmetricThresholdCircuit.wireCount
  rw [List.map_ofFn, List.sum_ofFn]
  rw [Finset.sum_add_distrib]
  simp

theorem thresholdCircuitOccurrences_wireCount {q : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit q) :
    occurrenceWireCount (thresholdCircuitOccurrences circuit) +
        (thresholdCircuitOccurrences circuit).length =
      circuit.wireCount := by
  unfold occurrenceWireCount thresholdCircuitOccurrences
    NormalizedThresholdThresholdCircuit.wireCount
  rw [List.map_ofFn, List.sum_ofFn]
  have henumerate :
      (∑ index : Fin circuit.top.support.card,
          (circuit.bottom (retainedTopIndex circuit index)).wireCount) =
        ∑ index ∈ circuit.top.support, (circuit.bottom index).wireCount := by
    let embedding : Fin circuit.top.support.card ↪ Fin circuit.bottomCount :=
      (retainedTopIndex circuit).toEmbedding
    have hmap :
        Finset.map embedding Finset.univ = circuit.top.support := by
      simp [embedding, retainedTopIndex]
    change
      (∑ index : Fin circuit.top.support.card,
          (circuit.bottom (embedding index)).wireCount) =
        ∑ index ∈ circuit.top.support, (circuit.bottom index).wireCount
    conv_rhs => rw [← hmap]
    exact (Finset.sum_map Finset.univ embedding
      (fun index => (circuit.bottom index).wireCount)).symm
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, List.length_ofFn]
  exact congrArg (fun wires => wires + circuit.top.support.card) henumerate

@[simp] theorem occurrenceWireCount_append {q : ℕ}
    (left right : List (SupportedNormalizedGate q)) :
    occurrenceWireCount (left ++ right) =
      occurrenceWireCount left + occurrenceWireCount right := by
  simp [occurrenceWireCount]

theorem symmetricFourfoldOccurrences_wireCount_le
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    occurrenceWireCount (symmetricFourfoldOccurrences request) ≤
      batchDescription NormalizedSymmetricThresholdCircuit.wireCount
        request.circuits := by
  change occurrenceWireCount
      (request.circuits.flatMap symmetricCircuitOccurrences) ≤
    (request.circuits.map
      NormalizedSymmetricThresholdCircuit.wireCount).sum
  induction request.circuits with
  | nil => simp [occurrenceWireCount]
  | cons circuit circuits inductionHypothesis =>
      simp only [List.flatMap_cons, occurrenceWireCount_append,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (by
          have := symmetricCircuitOccurrences_wireCount circuit
          omega)
        inductionHypothesis

theorem symmetricFourfoldOccurrences_wireCount
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    occurrenceWireCount (symmetricFourfoldOccurrences request) +
        (symmetricFourfoldOccurrences request).length =
      batchDescription NormalizedSymmetricThresholdCircuit.wireCount
        request.circuits := by
  change occurrenceWireCount
        (request.circuits.flatMap symmetricCircuitOccurrences) +
      (request.circuits.flatMap symmetricCircuitOccurrences).length =
    (request.circuits.map
      NormalizedSymmetricThresholdCircuit.wireCount).sum
  induction request.circuits with
  | nil => simp [occurrenceWireCount]
  | cons circuit circuits inductionHypothesis =>
      simp only [List.flatMap_cons, occurrenceWireCount_append,
        List.length_append, List.map_cons, List.sum_cons]
      rw [← symmetricCircuitOccurrences_wireCount circuit,
        ← inductionHypothesis]
      omega

theorem thresholdFourfoldOccurrences_wireCount_le
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    occurrenceWireCount (thresholdFourfoldOccurrences request) ≤
      batchDescription NormalizedThresholdThresholdCircuit.wireCount
        request.circuits := by
  change occurrenceWireCount
      (request.circuits.flatMap thresholdCircuitOccurrences) ≤
    (request.circuits.map
      NormalizedThresholdThresholdCircuit.wireCount).sum
  induction request.circuits with
  | nil => simp [occurrenceWireCount]
  | cons circuit circuits inductionHypothesis =>
      simp only [List.flatMap_cons, occurrenceWireCount_append,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (by
          have := thresholdCircuitOccurrences_wireCount circuit
          omega)
        inductionHypothesis

theorem thresholdFourfoldOccurrences_wireCount
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    occurrenceWireCount (thresholdFourfoldOccurrences request) +
        (thresholdFourfoldOccurrences request).length =
      batchDescription NormalizedThresholdThresholdCircuit.wireCount
        request.circuits := by
  change occurrenceWireCount
        (request.circuits.flatMap thresholdCircuitOccurrences) +
      (request.circuits.flatMap thresholdCircuitOccurrences).length =
    (request.circuits.map
      NormalizedThresholdThresholdCircuit.wireCount).sum
  induction request.circuits with
  | nil => simp [occurrenceWireCount]
  | cons circuit circuits inductionHypothesis =>
      simp only [List.flatMap_cons, occurrenceWireCount_append,
        List.length_append, List.map_cons, List.sum_cons]
      rw [← thresholdCircuitOccurrences_wireCount circuit,
        ← inductionHypothesis]
      omega

theorem batchDescription_le_card_mul
    {Circuit : Type} (description : Circuit → ℕ)
    (circuits : List Circuit) (cap : ℕ)
    (hcap : ∀ circuit ∈ circuits, description circuit ≤ cap) :
    batchDescription description circuits ≤ circuits.length * cap := by
  unfold batchDescription
  induction circuits with
  | nil => simp
  | cons circuit circuits inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hhead : description circuit ≤ cap := hcap circuit (by simp)
      have htail :
          ∀ candidate ∈ circuits, description candidate ≤ cap := by
        intro candidate hcandidate
        exact hcap candidate (by simp [hcandidate])
      calc
        description circuit +
            (List.map description circuits).sum ≤
            cap + circuits.length * cap :=
          Nat.add_le_add hhead (inductionHypothesis htail)
        _ = (circuits.length + 1) * cap := by ring

def normalizedLiveCount (q liveScale : ℕ) : ℕ :=
  min q (liveScale * logScale q)

theorem normalizedLiveCount_le (q liveScale : ℕ) :
    normalizedLiveCount q liveScale ≤ q :=
  min_le_left _ _

/-- Deterministic common live set for the complete occurrence pool. -/
def normalizedLiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) : Finset (Fin q) :=
  touchingSelect (occurrenceSupport occurrences)
    (normalizedLiveCount q liveScale)

/-! ### Canonical live/left/right assignment split -/

/-- Reindex a Boolean cube along one explicit sum of coordinate types.  This
is the only low-level splitting primitive used below; both directions are
equivalences, so no assignment is duplicated or discarded. -/
def bitInputSumEquiv {whole left right : ℕ}
    (coordinates : Fin left ⊕ Fin right ≃ Fin whole) :
    BitInput whole ≃ BitInput left × BitInput right :=
  (Equiv.arrowCongr coordinates.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin left) (Fin right) Bool)

/-- Increasing enumeration of a selected live set followed by its increasing
complement.  The construction is deterministic even when equal-support gates
induce several equally good touching sets. -/
def normalizedLiveExternalCoordinateEquiv {q : ℕ}
    (live : Finset (Fin q)) :
    Fin live.card ⊕ Fin liveᶜ.card ≃ Fin q :=
  finSumEquivOfFinset rfl rfl

def normalizedLiveExternalInputEquiv {q : ℕ}
    (live : Finset (Fin q)) :
    BitInput q ≃ BitInput live.card × BitInput liveᶜ.card :=
  bitInputSumEquiv (normalizedLiveExternalCoordinateEquiv live)

/-- The two external halves differ by at most one coordinate.  Keeping the
counts as named functions makes the eventual square-padding and runtime
ledger share exactly the same split. -/
def normalizedExternalLeftCount {q : ℕ}
    (live : Finset (Fin q)) : ℕ :=
  liveᶜ.card / 2

def normalizedExternalRightCount {q : ℕ}
    (live : Finset (Fin q)) : ℕ :=
  liveᶜ.card - normalizedExternalLeftCount live

theorem normalizedExternalCounts_add {q : ℕ}
    (live : Finset (Fin q)) :
    normalizedExternalLeftCount live +
        normalizedExternalRightCount live =
      liveᶜ.card := by
  unfold normalizedExternalLeftCount normalizedExternalRightCount
  exact Nat.add_sub_of_le (Nat.div_le_self _ _)

/-- Increasing prefix/suffix split of the non-live coordinates. -/
def normalizedExternalCoordinateEquiv {q : ℕ}
    (live : Finset (Fin q)) :
    Fin (normalizedExternalLeftCount live) ⊕
        Fin (normalizedExternalRightCount live) ≃
      Fin liveᶜ.card :=
  finSumFinEquiv.trans
    (finCongr (normalizedExternalCounts_add live))

def normalizedExternalLeftCoordinate {q : ℕ}
    (live : Finset (Fin q))
    (index : Fin (normalizedExternalLeftCount live)) : Fin q :=
  normalizedLiveExternalCoordinateEquiv live
    (.inr (normalizedExternalCoordinateEquiv live (.inl index)))

def normalizedExternalRightCoordinate {q : ℕ}
    (live : Finset (Fin q))
    (index : Fin (normalizedExternalRightCount live)) : Fin q :=
  normalizedLiveExternalCoordinateEquiv live
    (.inr (normalizedExternalCoordinateEquiv live (.inr index)))

/-! ### One normalized gate as a rectangular score table -/

/-- Little-endian enumeration of a Boolean cube by its exact binary address. -/
def bitInputIndexEquiv (bits : ℕ) :
    Fin (2 ^ bits) ≃ BitInput bits where
  toFun index := fun bit => index.val.testBit bit.val
  invFun := binaryAddress
  left_inv index := by
    exact binaryAddress_testBit index.isLt
  right_inv input := by
    funext bit
    change (binaryAddress input).val.testBit bit.val = input bit
    have haddress :
        (binaryAddress input).val = Nat.ofBits input := by
      unfold binaryAddress
      change encodeBitInput input % 2 ^ bits = Nat.ofBits input
      rw [encodeBitInput_eq_ofBits]
      exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow input)
    rw [haddress]
    exact Nat.testBit_ofBits_lt input bit.val bit.isLt

theorem normalizedExternalLeftCount_le_right {q : ℕ}
    (live : Finset (Fin q)) :
    normalizedExternalLeftCount live ≤
      normalizedExternalRightCount live := by
  unfold normalizedExternalLeftCount normalizedExternalRightCount
  apply Nat.le_sub_of_add_le
  simpa [normalizedExternalLeftCount, two_mul, Nat.mul_comm] using
    Nat.div_mul_le_self liveᶜ.card 2

theorem supportedLiveScore_eq_zero_of_disjoint
    {q : ℕ} (gate : SupportedNormalizedGate q)
    (live : Finset (Fin q))
    (hdisjoint : Disjoint live gate.support)
    (input : BitInput q) :
    liveScore gate.gate live input = 0 := by
  unfold liveScore
  apply Finset.sum_eq_zero
  intro index hindex
  have houtside : index ∉ gate.support := by
    exact fun hsupport =>
      (Finset.disjoint_left.mp hdisjoint) hindex hsupport
  rw [gate.zeroOutside index houtside]
  simp

theorem supportedMinimumLiveScore_eq_zero_of_disjoint
    {q : ℕ} (gate : SupportedNormalizedGate q)
    (live : Finset (Fin q))
    (hdisjoint : Disjoint live gate.support) :
    minimumLiveScore gate.gate live = 0 := by
  unfold minimumLiveScore
  apply Finset.sum_eq_zero
  intro index hindex
  have houtside : index ∉ gate.support := by
    exact fun hsupport =>
      (Finset.disjoint_left.mp hdisjoint) hindex hsupport
  rw [gate.zeroOutside index houtside]
  simp

/-- Untouched occurrences residualize identically to zero, which is the exact
sparsity fact consumed by the one common list compiler. -/
theorem residualVariable_eq_false_of_disjoint
    {q : ℕ} (gate : SupportedNormalizedGate q)
    (live : Finset (Fin q))
    (hdisjoint : Disjoint live gate.support)
    (input : BitInput q) :
    residualVariable gate.gate live input = false := by
  have hlive :=
    supportedLiveScore_eq_zero_of_disjoint gate live hdisjoint input
  have hminimum :=
    supportedMinimumLiveScore_eq_zero_of_disjoint gate live hdisjoint
  have hsplit := normalizedScore_split gate.gate live input
  have hfrozen :
      frozenScore gate.gate live input =
        ∑ index, gate.gate.weight index * bitInt (input index) := by
    rw [hlive] at hsplit
    simpa using hsplit.symm
  have hconstant :
      residualConstant gate.gate live input = gate.eval input := by
    unfold residualConstant SupportedNormalizedGate.eval
    rw [hminimum, Int.sub_zero, hfrozen]
    unfold NormalizedThresholdGate.eval
    rw [normalizedScore_eq_bitInt]
  unfold residualVariable
  rw [hconstant]
  unfold SupportedNormalizedGate.eval
  cases gate.gate.eval input <;> simp

/-- Exactly the physical occurrences whose supports meet the chosen live set. -/
def touchedOccurrences {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) : Finset (Fin occurrences.length) :=
  Finset.univ.filter fun index =>
    ¬Disjoint live (occurrenceSupport occurrences index)

theorem touchedOccurrences_card {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) :
    (touchedOccurrences occurrences live).card =
      touchingCost (occurrenceSupport occurrences) live := by
  classical
  unfold touchedOccurrences touchingCost touchIndicator
  symm
  calc
    (∑ index,
        if Disjoint live (occurrenceSupport occurrences index)
        then 0 else 1) =
        ∑ index,
          if ¬Disjoint live (occurrenceSupport occurrences index)
          then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro index _
            by_cases hdisjoint :
                Disjoint live (occurrenceSupport occurrences index)
            · simp [hdisjoint]
            · simp [hdisjoint]
    _ = (Finset.univ.filter fun index =>
          ¬Disjoint live (occurrenceSupport occurrences index)).card := by
      simpa using
        (Finset.sum_boole
          (R := ℕ)
          (fun index : Fin occurrences.length =>
            ¬Disjoint live (occurrenceSupport occurrences index))
          Finset.univ)

theorem residualVariable_eq_false_of_not_touched
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (index : Fin occurrences.length)
    (hindex : index ∉ touchedOccurrences occurrences live)
    (input : BitInput q) :
    residualVariable (occurrences.get index).gate live input = false := by
  have hdisjoint :
      Disjoint live (occurrenceSupport occurrences index) := by
    simpa [touchedOccurrences] using hindex
  exact residualVariable_eq_false_of_disjoint
    (occurrences.get index) live hdisjoint input

def occurrenceResidualConstant {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (index : Fin occurrences.length) : Bool :=
  residualConstant (occurrences.get index).gate live input

def occurrenceResidualVariable {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (index : Fin occurrences.length) : Bool :=
  residualVariable (occurrences.get index).gate live input

theorem occurrenceResidualVariable_eq_false_of_not_touched
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (index : Fin occurrences.length)
    (hindex : index ∉ touchedOccurrences occurrences live) :
    occurrenceResidualVariable occurrences live input index = false :=
  residualVariable_eq_false_of_not_touched
    occurrences live index hindex input

/-- The list input is the set of residual coordinates that are actually one
at this input.  It is a subset of the deterministic touching pool; using the
whole pool as the list input would lose the population-count semantics. -/
def occurrenceResidualActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q) :
    Finset (Fin occurrences.length) :=
  Finset.univ.filter fun index =>
    occurrenceResidualVariable occurrences
      (normalizedLiveSet occurrences liveScale) input index

theorem occurrenceResidualActiveSet_subset_touched {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q) :
    occurrenceResidualActiveSet occurrences liveScale input ⊆
      touchedOccurrences occurrences
        (normalizedLiveSet occurrences liveScale) := by
  intro index hactive
  have htrue :
      occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index = true :=
    (Finset.mem_filter.mp hactive).2
  by_contra hnotTouched
  have hfalse :=
    occurrenceResidualVariable_eq_false_of_not_touched
      occurrences (normalizedLiveSet occurrences liveScale)
      input index hnotTouched
  rw [hfalse] at htrue
  contradiction

theorem occurrenceResidualActiveSet_card_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q) :
    (occurrenceResidualActiveSet occurrences liveScale input).card ≤
      touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale) := by
  calc
    (occurrenceResidualActiveSet occurrences liveScale input).card ≤
        (touchedOccurrences occurrences
          (normalizedLiveSet occurrences liveScale)).card :=
      Finset.card_le_card
        (occurrenceResidualActiveSet_subset_touched
          occurrences liveScale input)
    _ = touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale) :=
      touchedOccurrences_card occurrences
        (normalizedLiveSet occurrences liveScale)

/-- A padded labelled sublist is represented by a position mask in the common
occurrence universe.  Intersecting with the actual residual-one set preserves
the shared labels and walk while keeping every unrelated coordinate zero. -/
def occurrenceMaskedResidualActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    Finset (Fin occurrences.length) :=
  occurrenceResidualActiveSet occurrences liveScale input ∩ mask

theorem occurrenceMaskedResidualActiveSet_card_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    (occurrenceMaskedResidualActiveSet occurrences liveScale input mask).card ≤
      touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (occurrenceResidualActiveSet_card_le occurrences liveScale input)

theorem occurrenceMaskedResidualActiveSet_card_eq_sum {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    (occurrenceMaskedResidualActiveSet occurrences liveScale input mask).card =
      ∑ index ∈ mask,
        (occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index).toNat := by
  have hinter :
      occurrenceMaskedResidualActiveSet occurrences liveScale input mask =
        mask.filter fun index =>
          occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index := by
    ext index
    simp [occurrenceMaskedResidualActiveSet,
      occurrenceResidualActiveSet, and_comm]
  rw [hinter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro index _
  cases occurrenceResidualVariable occurrences
      (normalizedLiveSet occurrences liveScale) input index <;> rfl

def occurrenceResidualConstantCount {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) : ℕ :=
  ∑ index ∈ mask,
    (occurrenceResidualConstant occurrences
      (normalizedLiveSet occurrences liveScale) input index).toNat

/-- Signed equation offset contributed by the deterministic residual constants.
This is shared by every threshold child equation; only `weight` changes. -/
def occurrenceWeightedResidualConstant {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (weight : Fin occurrences.length → ℤ) : ℤ :=
  ∑ index ∈ mask, weight index *
    bitInt (occurrenceResidualConstant occurrences
      (normalizedLiveSet occurrences liveScale) input index)

/-- Signed contribution represented by the sparse residual-one list. -/
def occurrenceWeightedResidualVariable {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (weight : Fin occurrences.length → ℤ) : ℤ :=
  ∑ index ∈ mask, weight index *
    bitInt (occurrenceResidualVariable occurrences
      (normalizedLiveSet occurrences liveScale) input index)

theorem occurrenceWeightedResidual_reconstruction {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (weight : Fin occurrences.length → ℤ) :
    occurrenceWeightedResidualConstant occurrences liveScale input mask weight +
        occurrenceWeightedResidualVariable occurrences liveScale input mask
          weight =
      ∑ index ∈ mask, weight index *
        bitInt ((occurrences.get index).eval input) := by
  unfold occurrenceWeightedResidualConstant
    occurrenceWeightedResidualVariable
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  have hnat :=
    residual_sum_reconstruction (occurrences.get index).gate
      (normalizedLiveSet occurrences liveScale) input
  have hint :
      bitInt (occurrenceResidualConstant occurrences
          (normalizedLiveSet occurrences liveScale) input index) +
        bitInt (occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index) =
        bitInt ((occurrences.get index).eval input) := by
    simp only [bitInt_eq_toNat, occurrenceResidualConstant,
      occurrenceResidualVariable]
    exact_mod_cast hnat
  rw [← hint]
  ring

theorem occurrenceResidualCount_reconstruction {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    occurrenceResidualConstantCount occurrences liveScale input mask +
        (occurrenceMaskedResidualActiveSet occurrences
          liveScale input mask).card =
      ∑ index ∈ mask, ((occurrences.get index).eval input).toNat := by
  rw [occurrenceMaskedResidualActiveSet_card_eq_sum]
  unfold occurrenceResidualConstantCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact residual_sum_reconstruction
    (occurrences.get index).gate
    (normalizedLiveSet occurrences liveScale) input

def normalizedMaskedResidualActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length)) :
    BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)) :=
  ⟨occurrenceMaskedResidualActiveSet occurrences liveScale input mask,
    occurrenceMaskedResidualActiveSet_card_le
      occurrences liveScale input mask⟩

/-- One binary coefficient plane of a masked residual equation.  A coordinate
is active exactly when its residual bit and the selected coefficient bit are
both one; carries are left to ordinary radix addition. -/
def occurrenceCoefficientBitActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    Finset (Fin occurrences.length) :=
  occurrenceResidualActiveSet occurrences liveScale input ∩
    (mask.filter fun index => (coefficient index).testBit bit)

theorem occurrenceCoefficientBitActiveSet_card_le {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    (occurrenceCoefficientBitActiveSet occurrences liveScale input
      mask coefficient bit).card ≤
        touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (occurrenceResidualActiveSet_card_le occurrences liveScale input)

theorem occurrenceCoefficientBitActiveSet_card_eq_sum {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    (occurrenceCoefficientBitActiveSet occurrences liveScale input
        mask coefficient bit).card =
      ∑ index ∈ mask,
        (occurrenceResidualVariable occurrences
            (normalizedLiveSet occurrences liveScale) input index &&
          (coefficient index).testBit bit).toNat := by
  have hinter :
      occurrenceCoefficientBitActiveSet occurrences liveScale input
          mask coefficient bit =
        mask.filter fun index =>
          occurrenceResidualVariable occurrences
              (normalizedLiveSet occurrences liveScale) input index &&
            (coefficient index).testBit bit := by
    ext index
    simp [occurrenceCoefficientBitActiveSet,
      occurrenceResidualActiveSet, and_left_comm]
  rw [hinter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro index _
  cases occurrenceResidualVariable occurrences
      (normalizedLiveSet occurrences liveScale) input index <;>
    cases (coefficient index).testBit bit <;>
    rfl

def normalizedCoefficientBitActiveSet {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ) (bit : ℕ) :
    BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)) :=
  ⟨occurrenceCoefficientBitActiveSet occurrences liveScale input
      mask coefficient bit,
    occurrenceCoefficientBitActiveSet_card_le
      occurrences liveScale input mask coefficient bit⟩

/-! ## Canonical circuit segments in the shared occurrence universe -/

/-- A contiguous segment of a canonical occurrence list.  Recording the exact
decomposition once avoids rebuilding parallel per-circuit occurrence lists:
all later masks are embeddings into the one shared universe. -/
structure ListSegment {α : Type} (all : List α) where
  before : List α
  body : List α
  after : List α
  decomposition : all = before ++ (body ++ after)

def ListSegment.embedding {α : Type} {all : List α}
    (segment : ListSegment all) : Fin segment.body.length ↪ Fin all.length where
  toFun index :=
    ⟨segment.before.length + index.val, by
      have hlength := congrArg List.length segment.decomposition
      simp only [List.length_append] at hlength
      omega⟩
  inj' := by
    intro left right hequal
    apply Fin.ext
    simpa using congrArg Fin.val hequal

def ListSegment.mask {α : Type} {all : List α}
    (segment : ListSegment all) : Finset (Fin all.length) :=
  Finset.univ.map segment.embedding

@[simp] theorem ListSegment.embedding_val
    {α : Type} {all : List α} (segment : ListSegment all)
    (index : Fin segment.body.length) :
    (segment.embedding index).val =
      segment.before.length + index.val :=
  rfl

@[simp] theorem ListSegment.mask_card
    {α : Type} {all : List α} (segment : ListSegment all) :
    segment.mask.card = segment.body.length := by
  simp [ListSegment.mask]

theorem ListSegment.get_embedding
    {α : Type} {all : List α} (segment : ListSegment all)
    (index : Fin segment.body.length) :
    all.get (segment.embedding index) = segment.body.get index := by
  rcases segment with ⟨before, body, after, decomposition⟩
  subst all
  change Fin body.length at index
  have hall :
      before.length + index.val <
        (before ++ (body ++ after)).length := by
    simp only [List.length_append]
    omega
  have hbody : index.val < body.length := index.isLt
  change
    (before ++ (body ++ after))[before.length + index.val]'hall =
      body[index.val]'hbody
  rw [List.getElem_append_right]
  · simp only [Nat.add_sub_cancel_left]
    apply List.getElem_append_left
  · omega

theorem ListSegment.sum_mask
    {α M : Type} [AddCommMonoid M] {all : List α}
    (segment : ListSegment all) (value : Fin all.length → M) :
    ∑ index ∈ segment.mask, value index =
      ∑ index : Fin segment.body.length,
        value (segment.embedding index) := by
  unfold ListSegment.mask
  rw [Finset.sum_map]

/-- The block occupied by one symmetric circuit in the flattened fourfold
occurrence list. -/
def symmetricCircuitSegment
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    ListSegment (symmetricFourfoldOccurrences request) where
  before :=
    (request.circuits.take circuitIndex.val).flatMap
      symmetricCircuitOccurrences
  body :=
    symmetricCircuitOccurrences (request.circuits.get circuitIndex)
  after :=
    (request.circuits.drop (circuitIndex.val + 1)).flatMap
      symmetricCircuitOccurrences
  decomposition := by
    unfold symmetricFourfoldOccurrences
    calc
      request.circuits.flatMap symmetricCircuitOccurrences =
          ((request.circuits.take circuitIndex.val) ++
            request.circuits.drop circuitIndex.val).flatMap
              symmetricCircuitOccurrences := by
        rw [List.take_append_drop]
      _ = ((request.circuits.take circuitIndex.val) ++
            (request.circuits.get circuitIndex ::
              request.circuits.drop (circuitIndex.val + 1))).flatMap
              symmetricCircuitOccurrences := by
        rw [List.drop_eq_getElem_cons circuitIndex.isLt]
        congr
      _ = (request.circuits.take circuitIndex.val).flatMap
              symmetricCircuitOccurrences ++
            (symmetricCircuitOccurrences
                (request.circuits.get circuitIndex) ++
              (request.circuits.drop (circuitIndex.val + 1)).flatMap
                symmetricCircuitOccurrences) := by
        simp only [List.flatMap_append, List.flatMap_cons]

/-- The corresponding retained-support block for one threshold-top circuit. -/
def thresholdCircuitSegment
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    ListSegment (thresholdFourfoldOccurrences request) where
  before :=
    (request.circuits.take circuitIndex.val).flatMap
      thresholdCircuitOccurrences
  body :=
    thresholdCircuitOccurrences (request.circuits.get circuitIndex)
  after :=
    (request.circuits.drop (circuitIndex.val + 1)).flatMap
      thresholdCircuitOccurrences
  decomposition := by
    unfold thresholdFourfoldOccurrences
    calc
      request.circuits.flatMap thresholdCircuitOccurrences =
          ((request.circuits.take circuitIndex.val) ++
            request.circuits.drop circuitIndex.val).flatMap
              thresholdCircuitOccurrences := by
        rw [List.take_append_drop]
      _ = ((request.circuits.take circuitIndex.val) ++
            (request.circuits.get circuitIndex ::
              request.circuits.drop (circuitIndex.val + 1))).flatMap
              thresholdCircuitOccurrences := by
        rw [List.drop_eq_getElem_cons circuitIndex.isLt]
        congr
      _ = (request.circuits.take circuitIndex.val).flatMap
              thresholdCircuitOccurrences ++
            (thresholdCircuitOccurrences
                (request.circuits.get circuitIndex) ++
              (request.circuits.drop (circuitIndex.val + 1)).flatMap
                thresholdCircuitOccurrences) := by
        simp only [List.flatMap_append, List.flatMap_cons]

@[simp] theorem thresholdCircuitSegment_body_length
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    (thresholdCircuitSegment request circuitIndex).body.length =
      (request.circuits.get circuitIndex).top.support.card := by
  simp [thresholdCircuitSegment, thresholdCircuitOccurrences]

/-- The exact embedding used by both a retained top child and its flattened
bottom-gate occurrence block. -/
def thresholdCircuitEmbedding
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    Fin (request.circuits.get circuitIndex).top.support.card ↪
      Fin (thresholdFourfoldOccurrences request).length :=
  (Fin.castOrderIso
      (thresholdCircuitSegment_body_length request circuitIndex).symm).toEmbedding.trans
    (thresholdCircuitSegment request circuitIndex).embedding

theorem thresholdCircuitEmbedding_get
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (index : Fin (request.circuits.get circuitIndex).top.support.card) :
    (thresholdFourfoldOccurrences request).get
        (thresholdCircuitEmbedding request circuitIndex index) =
      (request.circuits.get circuitIndex).bottom
        (retainedTopIndex (request.circuits.get circuitIndex) index) := by
  unfold thresholdCircuitEmbedding
  change
    (thresholdFourfoldOccurrences request).get
        ((thresholdCircuitSegment request circuitIndex).embedding
          ((Fin.castOrderIso
            (thresholdCircuitSegment_body_length request
              circuitIndex).symm) index)) =
      (request.circuits.get circuitIndex).bottom
        (retainedTopIndex (request.circuits.get circuitIndex) index)
  rw [ListSegment.get_embedding]
  simp only [thresholdCircuitSegment, thresholdCircuitOccurrences,
    List.get_ofFn]
  apply congrArg
  apply Fin.ext
  rfl

/-- Extend occurrence-local coefficients by zero along an embedding.  The
sum form avoids a choice-valued inverse and keeps duplicate physical blocks
distinguishable. -/
def embeddedWeight
    {Local Global : Type} [Fintype Local] [DecidableEq Global]
    (embedding : Local ↪ Global) (weight : Local → ℤ)
    (index : Global) : ℤ :=
  ∑ sourceIndex,
    if embedding sourceIndex = index then weight sourceIndex else 0

theorem embeddedWeight_score
    {Local Global : Type} [Fintype Local] [Fintype Global]
    [DecidableEq Global]
    (embedding : Local ↪ Global) (weight : Local → ℤ)
    (value : Global → ℤ) :
    (∑ index, embeddedWeight embedding weight index * value index) =
      ∑ sourceIndex, weight sourceIndex * value (embedding sourceIndex) := by
  unfold embeddedWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- One imported exact top child, represented over the single flattened
occurrence universe shared by every threshold row. -/
def thresholdChildEquation
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (child : ExactThresholdGate
      (request.circuits.get circuitIndex).top.support.card) :
    LabelledEquation (Fin (thresholdFourfoldOccurrences request).length) where
  weights :=
    embeddedWeight (thresholdCircuitEmbedding request circuitIndex) child.weight
  target := child.target

theorem thresholdChildEquation_score
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (child : ExactThresholdGate
      (request.circuits.get circuitIndex).top.support.card)
    (input : BitInput request.q) :
    (thresholdChildEquation request circuitIndex child).score
        (fun index =>
          ((thresholdFourfoldOccurrences request).get index).eval input) =
      ∑ sourceIndex, child.weight sourceIndex *
        bitInt (((request.circuits.get circuitIndex).bottom
          (retainedTopIndex
            (request.circuits.get circuitIndex) sourceIndex)).eval input) := by
  unfold LabelledEquation.score thresholdChildEquation
  rw [embeddedWeight_score]
  apply Finset.sum_congr rfl
  intro sourceIndex _
  change
    child.weight sourceIndex *
        bitInt (((thresholdFourfoldOccurrences request).get
          (thresholdCircuitEmbedding request circuitIndex sourceIndex)).eval
            input) =
      child.weight sourceIndex *
        bitInt (((request.circuits.get circuitIndex).bottom
          (retainedTopIndex
            (request.circuits.get circuitIndex) sourceIndex)).eval input)
  rw [thresholdCircuitEmbedding_get]

theorem thresholdChildEquation_holds_iff
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (child : ExactThresholdGate
      (request.circuits.get circuitIndex).top.support.card)
    (input : BitInput request.q) :
    (thresholdChildEquation request circuitIndex child).Holds
        (fun index =>
          ((thresholdFourfoldOccurrences request).get index).eval input) ↔
      child.eval
        (retainedBottomValues (request.circuits.get circuitIndex) input) =
          true := by
  unfold LabelledEquation.Holds LabelledEquation.difference
    ExactThresholdGate.eval
  rw [thresholdChildEquation_score]
  simp only [decide_eq_true_eq, sub_eq_zero]
  rfl

/-- Syntax-derived stack base.  Adding one makes the empty stack valid and
puts every represented signed digit strictly between `-base` and `base`. -/
def equationListBase
    {Carrier : Type} [Fintype Carrier]
    (equations : List (LabelledEquation Carrier)) : ℤ :=
  ((equations.map equationMagnitudeBound).sum + 1 : ℕ)

def canonicalEquationStack
    {Carrier : Type} [Fintype Carrier]
    (equations : List (LabelledEquation Carrier)) :
    LabelledEquation Carrier :=
  stackEquations (equationListBase equations) equations

private theorem equationMagnitudeBound_le_listSum
    {Carrier : Type} [Fintype Carrier]
    (equation : LabelledEquation Carrier)
    (equations : List (LabelledEquation Carrier))
    (hmember : equation ∈ equations) :
    equationMagnitudeBound equation ≤
      (equations.map equationMagnitudeBound).sum := by
  induction equations with
  | nil => simp at hmember
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hmember with rfl | htail
      · omega
      · have := inductionHypothesis htail
        omega

theorem canonicalEquationStack_holds_iff
    {Carrier : Type} [Fintype Carrier]
    (equations : List (LabelledEquation Carrier))
    (input : Carrier → Bool) :
    (canonicalEquationStack equations).Holds input ↔
      ∀ equation ∈ equations, equation.Holds input := by
  apply stackEquations_holds_iff
  · unfold equationListBase
    positivity
  · intro equation hmember
    have hmagnitude :=
      equation_difference_natAbs_le_magnitudeBound equation input
    have hmemberBound :=
      equationMagnitudeBound_le_listSum equation equations hmember
    have hnatAbs :
        (equation.difference input).natAbs <
          (equations.map equationMagnitudeBound).sum + 1 :=
      lt_of_le_of_lt (hmagnitude.trans hmemberBound) (Nat.lt_succ_self _)
    have habs :
        |equation.difference input| <
          equationListBase equations := by
      unfold equationListBase
      rw [← Int.natCast_natAbs]
      exact_mod_cast hnatAbs
    exact abs_lt.mp habs

/-! ## The aligned magnitude envelope dominates every selection stack
(ruling T2X-G*, ⚑ Dev veto open) -/

/-- The embedded child equation's magnitude is the raw child magnitude: the
segment embedding neither duplicates nor drops weight mass. -/
theorem thresholdChildEquation_magnitudeBound
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (child : ExactThresholdGate
      (request.circuits.get circuitIndex).top.support.card) :
    equationMagnitudeBound (thresholdChildEquation request circuitIndex child) =
      childMagnitude child := by
  unfold equationMagnitudeBound thresholdChildEquation childMagnitude
  simp only
  congr 1
  have hpointwise : ∀ sourceIndex :
      Fin (request.circuits.get circuitIndex).top.support.card,
      embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight
          (thresholdCircuitEmbedding request circuitIndex sourceIndex) =
        child.weight sourceIndex := by
    intro sourceIndex
    unfold embeddedWeight
    rw [Finset.sum_eq_single sourceIndex]
    · simp
    · intro candidate _ hcandidate
      rw [if_neg]
      intro hcontradiction
      exact hcandidate
        ((thresholdCircuitEmbedding request circuitIndex).injective
          hcontradiction)
    · intro habsent
      exact absurd (Finset.mem_univ sourceIndex) habsent
  have hoffBlock : ∀ index : Fin (thresholdFourfoldOccurrences request).length,
      index ∉ Finset.univ.map
          (thresholdCircuitEmbedding request circuitIndex) →
      embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight index = 0 := by
    intro index hmiss
    unfold embeddedWeight
    apply Finset.sum_eq_zero
    intro sourceIndex _
    rw [if_neg]
    intro hcontradiction
    exact hmiss (Finset.mem_map.mpr ⟨sourceIndex, Finset.mem_univ _,
      hcontradiction⟩)
  have hrestrict :
      (∑ index,
        (embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight index).natAbs) =
      ∑ index ∈ Finset.univ.map
          (thresholdCircuitEmbedding request circuitIndex),
        (embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight index).natAbs := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro index _ hmiss
    rw [hoffBlock index hmiss]
    rfl
  have hmapped :
      (∑ index ∈ Finset.univ.map
          (thresholdCircuitEmbedding request circuitIndex),
        (embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight index).natAbs) =
      ∑ sourceIndex,
        (embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight
          (thresholdCircuitEmbedding request circuitIndex
            sourceIndex)).natAbs :=
    Finset.sum_map _ _ _
  have hvalues :
      (∑ sourceIndex,
        (embeddedWeight (thresholdCircuitEmbedding request circuitIndex)
          child.weight
          (thresholdCircuitEmbedding request circuitIndex
            sourceIndex)).natAbs) =
      ∑ sourceIndex, (child.weight sourceIndex).natAbs := by
    apply Finset.sum_congr rfl
    intro sourceIndex _
    rw [hpointwise sourceIndex]
  rw [hrestrict, hmapped, hvalues]

theorem symmetricCircuitSegment_eval_sum
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (input : BitInput request.q) :
    (∑ index ∈ (symmetricCircuitSegment request circuitIndex).mask,
        (((symmetricFourfoldOccurrences request).get index).eval input).toNat) =
      ((request.circuits.get circuitIndex).acceptedBottomCount input).val := by
  rw [ListSegment.sum_mask]
  calc
    (∑ index : Fin (symmetricCircuitSegment request circuitIndex).body.length,
        (((symmetricFourfoldOccurrences request).get
          ((symmetricCircuitSegment request circuitIndex).embedding index)).eval
            input).toNat) =
        ∑ index : Fin (symmetricCircuitSegment request circuitIndex).body.length,
          (((symmetricCircuitSegment request circuitIndex).body.get index).eval
            input).toNat := by
      apply Finset.sum_congr rfl
      intro index _
      rw [ListSegment.get_embedding]
    _ = (((symmetricCircuitSegment request circuitIndex).body.map fun gate =>
          (gate.eval input).toNat).sum) := by
      have hget := congrArg
        (fun items =>
          (items.map fun gate => (gate.eval input).toNat).sum)
        (List.ofFn_get (symmetricCircuitSegment request circuitIndex).body)
      simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hget
    _ = ∑ index : Fin (request.circuits.get circuitIndex).bottomCount,
          (((request.circuits.get circuitIndex).bottom index).eval input).toNat := by
      simp only [symmetricCircuitSegment, symmetricCircuitOccurrences,
        List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    _ = ((request.circuits.get circuitIndex).acceptedBottomCount input).val := by
      change
        (∑ index,
          (((request.circuits.get circuitIndex).bottom index).eval input).toNat) =
        (Finset.univ.filter fun index =>
          ((request.circuits.get circuitIndex).bottom index).eval input).card
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro index _
      cases ((request.circuits.get circuitIndex).bottom index).eval input <;>
        rfl

def symmetricCircuitMask
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    Finset (Fin (symmetricFourfoldOccurrences request).length) :=
  (symmetricCircuitSegment request circuitIndex).mask

@[simp] theorem symmetricCircuitSegment_body_length
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    (symmetricCircuitSegment request circuitIndex).body.length =
      (request.circuits.get circuitIndex).bottomCount := by
  simp [symmetricCircuitSegment, symmetricCircuitOccurrences]

@[simp] theorem symmetricCircuitMask_card
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    (symmetricCircuitMask request circuitIndex).card =
      (request.circuits.get circuitIndex).bottomCount := by
  rw [symmetricCircuitMask, ListSegment.mask_card,
    symmetricCircuitSegment_body_length]

theorem symmetricCircuitResidualCount_reconstruction
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length) :
    occurrenceResidualConstantCount
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex) +
        (occurrenceMaskedResidualActiveSet
          (symmetricFourfoldOccurrences request) liveScale input
          (symmetricCircuitMask request circuitIndex)).card =
      ((request.circuits.get circuitIndex).acceptedBottomCount input).val := by
  rw [occurrenceResidualCount_reconstruction]
  exact symmetricCircuitSegment_eval_sum request circuitIndex input

/-- One canonical graded Toeplitz/walk certificate for the complete occurrence
pool.  All circuit modes differ only in which occurrence list they pass here. -/
abbrev NormalizedOccurrenceListSeed {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :=
  MargulisWalkSample
    (2 ^ toeplitzWalkSideBits
      (canonicalGradedRank occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale))))
    (canonicalWalkLength denominator)

noncomputable def normalizedOccurrenceListCertificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    AmplifiedListCertificate
      (BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (NormalizedOccurrenceListSeed occurrences liveScale denominator) :=
  tunedCanonicalGradedToeplitzPoweredWalkListCertificate spectrum
    occurrences.length
    (touchingCost (occurrenceSupport occurrences)
      (normalizedLiveSet occurrences liveScale))
    denominator

theorem normalizedOccurrenceListFailure_le
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    (normalizedOccurrenceListCertificate spectrum occurrences
      liveScale denominator).failure ≤
        1 / (denominator + 1 : ℕ) :=
  tunedCanonicalGradedToeplitzPoweredWalkListCertificate_failure_le
    spectrum occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale))
      denominator

/-! ## Toeplitz polynomials as exact printer rows -/

/-- Boolean presentation of the literal assignment used by the list
polynomial.  Keeping it adjacent to the `ZMod 2` assignment gives the printer
one canonical syntax boundary instead of a second semantic list evaluator. -/
def listLiteralBooleanAssignment
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) :
    ListLiteralVariable depth population → Bool
  | .terminal coordinate =>
      decide (coordinate ∈
        terminalLiteralActive active label seed depth)
  | .delta level slot =>
      decide (slot ∈
        deltaLiteralActive active label seed level.val)

theorem listLiteralAssignment_eq_boolean
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (literal : ListLiteralVariable depth population) :
    listLiteralAssignment active label seed literal =
      ((listLiteralBooleanAssignment active label seed literal).toNat :
        ZMod 2) := by
  cases literal with
  | terminal coordinate =>
      by_cases hmember :
          coordinate ∈ terminalLiteralActive active label seed depth <;>
        simp [listLiteralAssignment, listLiteralBooleanAssignment,
          SupplierWindow.bitAssignment, hmember]
  | delta level slot =>
      by_cases hmember :
          slot ∈ deltaLiteralActive active label seed level.val <;>
        simp [listLiteralAssignment, listLiteralBooleanAssignment,
          SupplierWindow.bitAssignment, hmember]

/-- One coordinate of the explicit Toeplitz list, after canonical expansion
to the occurrence-sensitive polynomial rows consumed by the score printer. -/
noncomputable def compiledListCoordinate
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) : Bool :=
  exactPolynomialValue
    (fun literal (_row : Unit) (_column : Unit) =>
      listLiteralBooleanAssignment active label seed literal)
    (polynomialMonomialOccurrences
      (listPolynomialVector label seed window terminalWindow candidate))
    () ()

theorem compiledListCoordinate_eq_of_succeeds
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1))
    (hsucceeds :
      polynomialListSucceeds active label window terminalWindow seed = true) :
    compiledListCoordinate active label seed window terminalWindow candidate =
      decide (candidate.val = active.card) := by
  have hcoordinates :
      ∀ candidate : Fin (population + 1),
        MvPolynomial.aeval
            (listLiteralAssignment (depth := depth) active label seed)
            (listPolynomialVector label seed window
              terminalWindow candidate) =
          if candidate.val = active.card then 1 else 0 := by
    unfold polynomialListSucceeds at hsucceeds
    exact of_decide_eq_true hsucceeds
  unfold compiledListCoordinate
  rw [exactPolynomialValue_compiled]
  have hassignment :
      (fun literal : ListLiteralVariable depth population =>
          ((listLiteralBooleanAssignment (depth := depth)
            active label seed literal).toNat : ZMod 2)) =
        listLiteralAssignment (depth := depth) active label seed := by
    funext literal
    exact (listLiteralAssignment_eq_boolean
      (depth := depth) active label seed literal).symm
  rw [hassignment, hcoordinates candidate]
  by_cases hcandidate : candidate.val = active.card <;>
    simp [hcandidate]

/-- Majority is defined on the complete Boolean vector, not by decoding list
outputs as integers.  This keeps malformed intermediate rows total. -/
def compiledBitMajority {t : ℕ} (bits : Fin t → Bool) : Bool :=
  decide (majorityThreshold t ≤
    ((Finset.univ : Finset (Fin t)).filter fun time =>
      bits time = true).card)

theorem compiledBitMajority_eq_of_mismatch_lt
    {t : ℕ} (ht : Odd t) (bits : Fin t → Bool) (target : Bool)
    (hmismatch :
      ((Finset.univ : Finset (Fin t)).filter fun time =>
        bits time != target).card < majorityThreshold t) :
    compiledBitMajority bits = target := by
  rcases ht with ⟨half, rfl⟩
  cases target with
  | false =>
      have htrue :
          ((Finset.univ : Finset (Fin (2 * half + 1))).filter fun time =>
            bits time = true).card <
              majorityThreshold (2 * half + 1) := by
        simpa using hmismatch
      unfold compiledBitMajority
      rw [decide_eq_false]
      omega
  | true =>
      let trueTimes :=
        (Finset.univ : Finset (Fin (2 * half + 1))).filter fun time =>
          bits time = true
      let falseTimes :=
        (Finset.univ : Finset (Fin (2 * half + 1))).filter fun time =>
          bits time = false
      have hfalse :
          falseTimes.card < majorityThreshold (2 * half + 1) := by
        simpa [falseTimes] using hmismatch
      have hpartition :
          trueTimes.card + falseTimes.card = 2 * half + 1 := by
        have hsplit :=
          Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin (2 * half + 1))))
            (p := fun time => bits time = true)
        have hnot :
            ((Finset.univ : Finset (Fin (2 * half + 1))).filter fun time =>
              ¬bits time = true) = falseTimes := by
          ext time
          cases bits time <;> simp [falseTimes]
        simpa [trueTimes, hnot] using hsplit
      have hmajority :
          majorityThreshold (2 * half + 1) ≤ trueTimes.card := by
        unfold majorityThreshold at hfalse ⊢
        omega
      unfold compiledBitMajority
      rw [decide_eq_true]
      exact hmajority

/-- Coordinatewise powered-walk majority of the already-compiled base list
rows.  Every visited seed is recovered through the one canonical
vertex-to-Toeplitz encoding. -/
noncomputable def compiledWalkListCoordinate
    {rank depth population t : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1)) : Bool :=
  compiledBitMajority fun time =>
    compiledListCoordinate active label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate

theorem compiledWalkListCoordinate_eq_of_succeeds
    {rank depth population activeBound t : ℕ}
    (ht : Odd t)
    (input : BoundedActiveSet population activeBound)
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (sample : MargulisWalkSample
      (2 ^ toeplitzWalkSideBits rank) t)
    (candidate : Fin (population + 1))
    (hsucceeds :
      concreteMajorityFailure
        (fun vertex =>
          !(toeplitzVertexSucceeds label window terminalWindow input vertex))
        sample = false) :
    compiledWalkListCoordinate input.1 label window terminalWindow
        sample candidate =
      decide (candidate.val = input.1.card) := by
  let target := decide (candidate.val = input.1.card)
  let bits : Fin t → Bool := fun time =>
    compiledListCoordinate input.1 label
      (toeplitzWalkEncoding rank (sample.vertex time)).1
      window terminalWindow candidate
  let bad :
      MargulisVertex (2 ^ toeplitzWalkSideBits rank) → Bool :=
    fun vertex =>
      !(toeplitzVertexSucceeds label window terminalWindow input vertex)
  let mismatchTimes :=
    (Finset.univ : Finset (Fin t)).filter fun time =>
      bits time != target
  have hbadCard :
      (concreteBadTimes bad sample).card < majorityThreshold t := by
    have hfailure :
        concreteMajorityFailure bad sample = false := by
      simpa [bad] using hsucceeds
    unfold concreteMajorityFailure at hfailure
    exact Nat.lt_of_not_ge (of_decide_eq_false hfailure)
  have hmismatchSubset :
      mismatchTimes ⊆ concreteBadTimes bad sample := by
    intro time htime
    have hmismatch :
        (bits time != target) = true := (Finset.mem_filter.mp htime).2
    have himplies :
        (bits time != target) = true →
          bad (sample.vertex time) = true := by
      intro _
      cases hsucceed :
          toeplitzVertexSucceeds label window terminalWindow input
            (sample.vertex time) with
      | false => simp [bad, hsucceed]
      | true =>
          have hbase :
              polynomialListSucceeds input.1 label window terminalWindow
                  (toeplitzWalkEncoding rank (sample.vertex time)).1 =
                true := by
            simpa [toeplitzVertexSucceeds] using hsucceed
          have hequal :=
            compiledListCoordinate_eq_of_succeeds input.1 label
              (toeplitzWalkEncoding rank (sample.vertex time)).1
              window terminalWindow candidate hbase
          have hcontra : False := by
            dsimp [bits, target] at hmismatch
            rw [hequal] at hmismatch
            simp at hmismatch
          exact hcontra.elim
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ time, by
        unfold concreteBadAt
        exact himplies hmismatch⟩
  have hmismatch :
      mismatchTimes.card < majorityThreshold t :=
    lt_of_le_of_lt (Finset.card_le_card hmismatchSubset) hbadCard
  unfold compiledWalkListCoordinate
  apply compiledBitMajority_eq_of_mismatch_lt ht bits target
  simpa [mismatchTimes] using hmismatch

/-- The sole production list coordinate: canonical rank, labels, graded
windows, walk length, and occurrence-sensitive polynomial compiler. -/
noncomputable def canonicalOccurrenceListCoordinate
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1)) : Bool :=
  compiledWalkListCoordinate
    (depth := canonicalGradedDepth
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    active.1
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (gradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    gradedTerminalWindow sample candidate

theorem compiledCanonicalOccurrenceListCoordinate_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (candidate : Fin (occurrences.length + 1))
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds
          active sample = true) :
    canonicalOccurrenceListCoordinate occurrences liveScale denominator
        active sample candidate =
      decide (candidate.val =
        active.1.card) := by
  unfold canonicalOccurrenceListCoordinate
  apply compiledWalkListCoordinate_eq_of_succeeds
    (canonicalWalkLength_odd denominator)
    active
    (canonicalGradedLabel occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (gradedWindow
      (depth := canonicalGradedDepth
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    gradedTerminalWindow sample candidate
  apply Bool.eq_false_of_not_eq_true'
  simpa only [normalizedOccurrenceListCertificate,
    tunedCanonicalGradedToeplitzPoweredWalkListCertificate,
    gradedToeplitzPoweredWalkListCertificate,
    toeplitzPoweredWalkListCertificate,
    concretePoweredWalkListCertificate] using hsucceeds

/-- Total scalar lookup selected by a one-hot vector.  Parity is the unique
`𝔽₂` row semantics on malformed vectors and agrees with ordinary selection on
the exact vector. -/
def oneHotLookupRow {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot : Fin (populationBound + 1) → Bool) : Bool :=
  boolParity fun candidate => oneHot candidate && lookup candidate

theorem oneHotLookupRow_eq_of_oneHot
    {populationBound : ℕ}
    (lookup : Fin (populationBound + 1) → Bool)
    (oneHot : Fin (populationBound + 1) → Bool)
    (actual : Fin (populationBound + 1))
    (honeHot : ∀ candidate,
      oneHot candidate = decide (candidate = actual)) :
    oneHotLookupRow lookup oneHot = lookup actual := by
  unfold oneHotLookupRow
  have hequal :
      (fun candidate => oneHot candidate && lookup candidate) =
        fun candidate => decide (candidate = actual) && lookup candidate := by
    funext candidate
    rw [honeHot candidate]
  rw [hequal]
  exact boolParity_exactSelector actual lookup

/-- Total offset lookup used by symmetric tops.  Out-of-range values on
malformed list vectors map to false; the legal residual count is proved
in-range before the top table is read. -/
def shiftedFiniteLookup {population bound : ℕ}
    (offset : ℕ) (lookup : Fin (bound + 1) → Bool)
    (candidate : Fin (population + 1)) : Bool :=
  if hbound : offset + candidate.val < bound + 1 then
    lookup ⟨offset + candidate.val, hbound⟩
  else
    false

theorem shiftedFiniteLookup_eq
    {population bound offset total : ℕ}
    (lookup : Fin (bound + 1) → Bool)
    (candidate : Fin (population + 1))
    (htotal : offset + candidate.val = total)
    (htotalBound : total < bound + 1) :
    shiftedFiniteLookup offset lookup candidate =
      lookup ⟨total, htotalBound⟩ := by
  unfold shiftedFiniteLookup
  rw [dif_pos (htotal ▸ htotalBound)]
  congr

/-- The bounded active-set cardinality as a legal lookup coordinate. -/
def boundedActiveCard {population activeBound : ℕ}
    (active : BoundedActiveSet population activeBound) :
    Fin (population + 1) :=
  ⟨active.1.card,
    Nat.lt_succ_of_le (by simpa using Finset.card_le_univ active.1)⟩

/-- Direct symmetric lookup row over the same canonical list output used by
the modular-radix path. -/
noncomputable def canonicalOccurrenceLookupRow
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool) : Bool :=
  oneHotLookupRow lookup fun candidate =>
    canonicalOccurrenceListCoordinate occurrences liveScale denominator
      active sample candidate

theorem canonicalOccurrenceLookupRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (lookup : Fin (occurrences.length + 1) → Bool)
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds active sample = true) :
    canonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample lookup =
      lookup (boundedActiveCard active) := by
  unfold canonicalOccurrenceLookupRow
  apply oneHotLookupRow_eq_of_oneHot lookup _
    (boundedActiveCard active)
  intro candidate
  rw [compiledCanonicalOccurrenceListCoordinate_eq_of_certificate
    spectrum occurrences liveScale denominator active sample
      candidate hsucceeds]
  apply decide_eq_decide.mpr
  constructor
  · intro hvalue
    apply Fin.ext
    exact hvalue
  · intro hequal
    exact congrArg Fin.val hequal

theorem canonicalOccurrenceShiftedLookupRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : BoundedActiveSet occurrences.length
      (touchingCost (occurrenceSupport occurrences)
        (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (offset total : ℕ)
    (lookup : Fin (occurrences.length + 1) → Bool)
    (htotal : offset + active.1.card = total)
    (htotalBound : total < occurrences.length + 1)
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds active sample = true) :
    canonicalOccurrenceLookupRow occurrences liveScale denominator
        active sample (shiftedFiniteLookup offset lookup) =
      lookup ⟨total, htotalBound⟩ := by
  rw [canonicalOccurrenceLookupRow_eq_of_certificate spectrum
    occurrences liveScale denominator active sample
      (shiftedFiniteLookup offset lookup) hsucceeds]
  apply shiftedFiniteLookup_eq lookup (boundedActiveCard active)
  simpa [boundedActiveCard] using htotal

/-- The accepted count of one symmetric circuit, embedded in the common
occurrence-count coordinate space. -/
def symmetricAcceptedCountInOccurrences
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (input : BitInput request.q) :
    Fin ((symmetricFourfoldOccurrences request).length + 1) :=
  ⟨((request.circuits.get circuitIndex).acceptedBottomCount input).val, by
    have hbottom :
        (request.circuits.get circuitIndex).bottomCount ≤
          (symmetricFourfoldOccurrences request).length := by
      rw [← symmetricCircuitMask_card request circuitIndex]
      simpa using Finset.card_le_card
        (Finset.subset_univ (symmetricCircuitMask request circuitIndex))
    exact ((request.circuits.get circuitIndex).acceptedBottomCount input).isLt.trans_le
      (Nat.succ_le_succ hbottom)⟩

/-- A symmetric top table lifted to the common occurrence-count space.  The
false overflow branch is reachable only on malformed list outputs. -/
def symmetricCircuitTopLookup
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length) :
    Fin ((symmetricFourfoldOccurrences request).length + 1) → Bool :=
  fun candidate =>
    if hbound :
        candidate.val < (request.circuits.get circuitIndex).bottomCount + 1 then
      (request.circuits.get circuitIndex).top ⟨candidate.val, hbound⟩
    else
      false

theorem symmetricCircuitTopLookup_accepted
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (circuitIndex : Fin request.circuits.length)
    (input : BitInput request.q) :
    symmetricCircuitTopLookup request circuitIndex
        (symmetricAcceptedCountInOccurrences request circuitIndex input) =
      (request.circuits.get circuitIndex).eval input := by
  unfold symmetricCircuitTopLookup
    symmetricAcceptedCountInOccurrences
    NormalizedSymmetricThresholdCircuit.eval
  rw [dif_pos
    ((request.circuits.get circuitIndex).acceptedBottomCount input).isLt]

/-- One circuit row of the symmetric supplier.  Constants, the amplified list,
and the top lookup all read the same flattened occurrence pool. -/
noncomputable def canonicalSymmetricCircuitRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  canonicalOccurrenceLookupRow
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

theorem canonicalSymmetricCircuitRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (circuitIndex : Fin request.circuits.length)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (hsucceeds :
      (normalizedOccurrenceListCertificate spectrum
        (symmetricFourfoldOccurrences request) liveScale denominator).succeeds
          (normalizedMaskedResidualActiveSet
            (symmetricFourfoldOccurrences request) liveScale input
            (symmetricCircuitMask request circuitIndex)) sample = true) :
    canonicalSymmetricCircuitRow request liveScale denominator input
        circuitIndex sample =
      (request.circuits.get circuitIndex).eval input := by
  unfold canonicalSymmetricCircuitRow
  rw [canonicalOccurrenceShiftedLookupRow_eq_of_certificate spectrum
    (symmetricFourfoldOccurrences request) liveScale denominator
    (normalizedMaskedResidualActiveSet
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    sample
    (occurrenceResidualConstantCount
      (symmetricFourfoldOccurrences request) liveScale input
      (symmetricCircuitMask request circuitIndex))
    ((request.circuits.get circuitIndex).acceptedBottomCount input).val
    (symmetricCircuitTopLookup request circuitIndex)
    (symmetricCircuitResidualCount_reconstruction
      request liveScale input circuitIndex)
    (symmetricAcceptedCountInOccurrences request circuitIndex input).isLt
    hsucceeds]
  exact symmetricCircuitTopLookup_accepted request circuitIndex input

def finiteBoolConjunction
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (value : Label → Bool) : Bool :=
  decide (∀ label, value label = true)

theorem finiteBoolConjunction_eq_true_iff
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (value : Label → Bool) :
    finiteBoolConjunction value = true ↔
      ∀ label, value label = true := by
  unfold finiteBoolConjunction
  exact decide_eq_true_iff

theorem finiteBoolConjunction_congr
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (left right : Label → Bool)
    (hequal : ∀ label, left label = right label) :
    finiteBoolConjunction left = finiteBoolConjunction right := by
  congr 1
  funext label
  exact hequal label

def finiteBoolDisjunction
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (value : Label → Bool) : Bool :=
  decide (∃ label, value label = true)

theorem finiteBoolDisjunction_eq_true_iff
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (value : Label → Bool) :
    finiteBoolDisjunction value = true ↔
      ∃ label, value label = true := by
  unfold finiteBoolDisjunction
  exact decide_eq_true_iff

theorem finiteBoolDisjunction_congr
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (left right : Label → Bool)
    (hequal : ∀ label, left label = right label) :
    finiteBoolDisjunction left = finiteBoolDisjunction right := by
  congr 1
  funext label
  exact hequal label

theorem finiteBoolConjunction_get_eq_conjunctionBit
    {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool)
    (circuits : List Circuit) (input : BitInput q) :
    finiteBoolConjunction
        (fun index : Fin circuits.length => evaluate (circuits.get index) input) =
      conjunctionBit evaluate circuits input := by
  have hleft :
      finiteBoolConjunction
          (fun index : Fin circuits.length =>
            evaluate (circuits.get index) input) = true ↔
        ∀ index : Fin circuits.length,
          evaluate (circuits.get index) input = true := by
    exact finiteBoolConjunction_eq_true_iff _
  have hright :
      conjunctionBit evaluate circuits input = true ↔
        ∀ index : Fin circuits.length,
          evaluate (circuits.get index) input = true := by
    unfold conjunctionBit
    rw [List.all_eq_true, List.forall_mem_iff_get]
  exact Bool.eq_iff_iff.mpr (hleft.trans hright.symm)

/-- The complete symmetric row is the conjunction of the circuit segments;
all segments reuse one list seed and one flattened occurrence universe. -/
noncomputable def canonicalSymmetricFourfoldRow
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator) : Bool :=
  finiteBoolConjunction fun circuitIndex : Fin request.circuits.length =>
    canonicalSymmetricCircuitRow request liveScale denominator input
      circuitIndex sample

theorem canonicalSymmetricFourfoldRow_eq_of_certificate
    (spectrum : ExpanderSpectrumContract)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (hsucceeds : ∀ circuitIndex : Fin request.circuits.length,
      (normalizedOccurrenceListCertificate spectrum
        (symmetricFourfoldOccurrences request) liveScale denominator).succeeds
          (normalizedMaskedResidualActiveSet
            (symmetricFourfoldOccurrences request) liveScale input
            (symmetricCircuitMask request circuitIndex)) sample = true) :
    canonicalSymmetricFourfoldRow request liveScale denominator input sample =
      conjunctionBit NormalizedSymmetricThresholdCircuit.eval
        request.circuits input := by
  unfold canonicalSymmetricFourfoldRow
  calc
    finiteBoolConjunction
        (fun circuitIndex : Fin request.circuits.length =>
          canonicalSymmetricCircuitRow request liveScale denominator input
            circuitIndex sample) =
        finiteBoolConjunction
          (fun circuitIndex : Fin request.circuits.length =>
            (request.circuits.get circuitIndex).eval input) := by
      apply finiteBoolConjunction_congr
      intro circuitIndex
      exact canonicalSymmetricCircuitRow_eq_of_certificate spectrum request
        liveScale denominator input circuitIndex sample
          (hsucceeds circuitIndex)
    _ = conjunctionBit NormalizedSymmetricThresholdCircuit.eval
          request.circuits input :=
      finiteBoolConjunction_get_eq_conjunctionBit
        NormalizedSymmetricThresholdCircuit.eval request.circuits input

theorem canonicalSymmetricFourfoldRow_mismatch_reciprocal
    (spectrum : ExpanderSpectrumContract)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale denominator : ℕ) (input : BitInput request.q) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            (symmetricFourfoldOccurrences request) liveScale denominator =>
          canonicalSymmetricFourfoldRow request liveScale denominator
              input sample !=
            conjunctionBit NormalizedSymmetricThresholdCircuit.eval
              request.circuits input) ≤
      request.circuits.length / (denominator + 1 : ℕ) := by
  let certificate :=
    normalizedOccurrenceListCertificate spectrum
      (symmetricFourfoldOccurrences request) liveScale denominator
  calc
    _ ≤ Fintype.card (Fin request.circuits.length) * certificate.failure := by
      apply booleanMean_unionBound_uniform
        (fun sample : NormalizedOccurrenceListSeed
            (symmetricFourfoldOccurrences request) liveScale denominator =>
          canonicalSymmetricFourfoldRow request liveScale denominator
              input sample !=
            conjunctionBit NormalizedSymmetricThresholdCircuit.eval
              request.circuits input)
        (fun circuitIndex sample =>
          !(certificate.succeeds
            (normalizedMaskedResidualActiveSet
              (symmetricFourfoldOccurrences request) liveScale input
              (symmetricCircuitMask request circuitIndex)) sample))
        certificate.failure
      · intro sample hmismatch
        by_contra hnone
        have hall : ∀ circuitIndex : Fin request.circuits.length,
            certificate.succeeds
              (normalizedMaskedResidualActiveSet
                (symmetricFourfoldOccurrences request) liveScale input
                (symmetricCircuitMask request circuitIndex)) sample = true := by
          intro circuitIndex
          cases hvalue : certificate.succeeds
              (normalizedMaskedResidualActiveSet
                (symmetricFourfoldOccurrences request) liveScale input
                (symmetricCircuitMask request circuitIndex)) sample
          · exfalso
            apply hnone
            exact ⟨circuitIndex, by simp [hvalue]⟩
          · rfl
        have hequal :=
          canonicalSymmetricFourfoldRow_eq_of_certificate spectrum request
            liveScale denominator input sample hall
        rw [hequal] at hmismatch
        simp at hmismatch
      · intro circuitIndex
        exact certificate.pointwise
          (normalizedMaskedResidualActiveSet
            (symmetricFourfoldOccurrences request) liveScale input
            (symmetricCircuitMask request circuitIndex))
    _ ≤ Fintype.card (Fin request.circuits.length) *
          (1 / (denominator + 1 : ℕ)) := by
      gcongr
      exact normalizedOccurrenceListFailure_le spectrum
        (symmetricFourfoldOccurrences request) liveScale denominator
    _ = request.circuits.length / (denominator + 1 : ℕ) := by
      simp only [Fintype.card_fin]
      ring

/-- The actual population represented by one bounded labelled sublist. -/
def boundedActivePopulation
    {population activeBound digits : ℕ}
    (active : Fin digits → BoundedActiveSet population activeBound) :
    Fin digits → Fin (population + 1) :=
  fun digit =>
    boundedActiveCard (active digit)

/-- Binary coefficient planes reassemble to the exact sparse weighted score.
The theorem permits ordinary carries: list outputs supply digit populations,
while `radixValue` performs the complete integer addition before reduction. -/
theorem coefficientBitRadixValue_eq
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (hcoefficient : ∀ index, coefficient index < 2 ^ digits) :
    radixValue 2
        (boundedActivePopulation fun digit : Fin digits =>
          normalizedCoefficientBitActiveSet occurrences liveScale input
            mask coefficient digit.val) =
      ∑ index ∈ mask, coefficient index *
        (occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index).toNat := by
  let residual : Fin occurrences.length → Bool :=
    fun index =>
      decide (index ∈ mask) &&
        occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index
  let digit : Fin occurrences.length → Fin digits → ℕ :=
    fun index place => ((coefficient index).testBit place.val).toNat
  have hreconstruct : ∀ index,
      coefficient index =
        ∑ place : Fin digits, 2 ^ place.val * digit index place := by
    intro index
    calc
      coefficient index =
          ∑ place : Fin digits,
            ((coefficient index).testBit place.val).toNat *
              2 ^ place.val :=
        (testBit_toNat_sum_eq (hcoefficient index)).symm
      _ = ∑ place : Fin digits,
            2 ^ place.val * digit index place := by
        apply Finset.sum_congr rfl
        intro place _
        dsimp [digit]
        ring
  have hscore :=
    radixScore_eq_digitPopulations 2 coefficient digit residual hreconstruct
  symm
  calc
    (∑ index ∈ mask, coefficient index *
        (occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index).toNat) =
        ∑ index : Fin occurrences.length,
          coefficient index * (residual index).toNat := by
      calc
        _ = ∑ index ∈
              (Finset.univ.filter fun index : Fin occurrences.length =>
                index ∈ mask),
              coefficient index *
                (occurrenceResidualVariable occurrences
                  (normalizedLiveSet occurrences liveScale) input
                    index).toNat := by
          simp
        _ = ∑ index : Fin occurrences.length,
              if index ∈ mask then
                coefficient index *
                  (occurrenceResidualVariable occurrences
                    (normalizedLiveSet occurrences liveScale) input
                      index).toNat
              else 0 :=
          Finset.sum_filter _ _
        _ = ∑ index : Fin occurrences.length,
              coefficient index * (residual index).toNat := by
          apply Finset.sum_congr rfl
          intro index _
          by_cases hmember : index ∈ mask
          · simp [residual, hmember]
          · simp [residual, hmember]
    _ = ∑ place : Fin digits, 2 ^ place.val *
          digitPopulation digit residual place :=
      hscore
    _ = radixValue 2
        (boundedActivePopulation fun place : Fin digits =>
          normalizedCoefficientBitActiveSet occurrences liveScale input
            mask coefficient place.val) := by
      unfold radixValue boundedActivePopulation boundedActiveCard
      apply Finset.sum_congr rfl
      intro place _
      congr 1
      change digitPopulation digit residual place =
        (occurrenceCoefficientBitActiveSet occurrences liveScale input
          mask coefficient place.val).card
      rw [occurrenceCoefficientBitActiveSet_card_eq_sum]
      unfold digitPopulation
      calc
        (∑ index : Fin occurrences.length,
            digit index place * (residual index).toNat) =
            ∑ index ∈
              (Finset.univ.filter fun index : Fin occurrences.length =>
                index ∈ mask),
              (occurrenceResidualVariable occurrences
                    (normalizedLiveSet occurrences liveScale) input index &&
                (coefficient index).testBit place.val).toNat := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro index _
          by_cases hmember : index ∈ mask
          · cases hresidual :
                occurrenceResidualVariable occurrences
                  (normalizedLiveSet occurrences liveScale) input index <;>
              cases hbit : (coefficient index).testBit place.val <;>
              simp [digit, residual, hmember, hresidual, hbit]
          · simp [digit, residual, hmember]
        _ = ∑ index ∈ mask,
              (occurrenceResidualVariable occurrences
                    (normalizedLiveSet occurrences liveScale) input index &&
                (coefficient index).testBit place.val).toNat := by
          simp

/-- Canonical nonnegative representative of one signed coefficient modulo a
positive natural modulus. -/
def modularCoefficientResidue
    {Carrier : Type} (equation : LabelledEquation Carrier)
    (modulus : ℕ) (index : Carrier) : ℕ :=
  (equation.weights index % (modulus : ℤ)).toNat

/-- The deterministic residual constants and equation target are folded into
the modular offset; list rows need only print sparse variable populations. -/
def modularResidualOffset
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (equation : LabelledEquation (Fin occurrences.length))
    (modulus : ℕ) : ℕ :=
  ((occurrenceWeightedResidualConstant occurrences liveScale input
      Finset.univ equation.weights - equation.target) %
        (modulus : ℤ)).toNat

theorem modularCoefficientResidue_lt
    {Carrier : Type} (equation : LabelledEquation Carrier)
    (modulus : ℕ) (hmodulus : 0 < modulus) (index : Carrier) :
    modularCoefficientResidue equation modulus index <
      2 ^ (Nat.log 2 modulus).succ := by
  have hmodulusInt : (0 : ℤ) < modulus := by exact_mod_cast hmodulus
  have hnonnegative :
      0 ≤ equation.weights index % (modulus : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hmodulusInt)
  have hbelow :
      equation.weights index % (modulus : ℤ) < (modulus : ℤ) :=
    Int.emod_lt_of_pos _ hmodulusInt
  have hresidue :
      modularCoefficientResidue equation modulus index < modulus := by
    unfold modularCoefficientResidue
    exact (Int.toNat_lt hnonnegative).mpr hbelow
  exact hresidue.trans (Nat.lt_pow_succ_log_self (by omega) modulus)

/-- Signed coefficients, constants, and targets are represented exactly
modulo `modulus`; no unsigned conversion is trusted without this bridge. -/
theorem modularResidualEquation_spec
    {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (input : BitInput q)
    (equation : LabelledEquation (Fin occurrences.length))
    (modulus : ℕ) (hmodulus : 0 < modulus) :
    ((modularResidualOffset occurrences liveScale input equation modulus +
          ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
            modularCoefficientResidue equation modulus index *
              (occurrenceResidualVariable occurrences
                (normalizedLiveSet occurrences liveScale) input index).toNat) %
        modulus = 0) ↔
      equation.HoldsModulo (modulus : ℤ)
        (fun index => (occurrences.get index).eval input) := by
  let variableBit : Fin occurrences.length → Bool :=
    fun index =>
      occurrenceResidualVariable occurrences
        (normalizedLiveSet occurrences liveScale) input index
  let constantDifference : ℤ :=
    occurrenceWeightedResidualConstant occurrences liveScale input
      Finset.univ equation.weights - equation.target
  let variableScore : ℤ :=
    occurrenceWeightedResidualVariable occurrences liveScale input
      Finset.univ equation.weights
  have hmodulusInt : (0 : ℤ) < modulus := by exact_mod_cast hmodulus
  have hcoefficient :
      ∀ index : Fin occurrences.length,
        ((modularCoefficientResidue equation modulus index : ℕ) : ℤ) ≡
          equation.weights index [ZMOD (modulus : ℤ)] := by
    intro index
    unfold modularCoefficientResidue
    rw [Int.toNat_of_nonneg
      (Int.emod_nonneg _ (ne_of_gt hmodulusInt))]
    exact Int.mod_modEq _ _
  have hvariable :
      ((∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
          modularCoefficientResidue equation modulus index *
            (variableBit index).toNat : ℕ) : ℤ) ≡
        variableScore [ZMOD (modulus : ℤ)] := by
    unfold variableScore occurrenceWeightedResidualVariable
    push_cast
    apply Int.ModEq.sum
    intro index _
    apply Int.ModEq.mul
    · exact hcoefficient index
    · simp [variableBit, bitInt_eq_toNat]
  have hoffset :
      ((modularResidualOffset occurrences liveScale input equation modulus :
          ℕ) : ℤ) ≡ constantDifference [ZMOD (modulus : ℤ)] := by
    unfold modularResidualOffset constantDifference
    rw [Int.toNat_of_nonneg
      (Int.emod_nonneg _ (ne_of_gt hmodulusInt))]
    exact Int.mod_modEq _ _
  have hcombined :
      (((modularResidualOffset occurrences liveScale input equation modulus +
          ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
            modularCoefficientResidue equation modulus index *
              (variableBit index).toNat : ℕ) : ℕ) : ℤ) ≡
        constantDifference + variableScore [ZMOD (modulus : ℤ)] := by
    change
      ((modularResidualOffset occurrences liveScale input equation modulus :
          ℕ) : ℤ) +
        ((∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
          modularCoefficientResidue equation modulus index *
            (variableBit index).toNat : ℕ) : ℤ) ≡
        constantDifference + variableScore [ZMOD (modulus : ℤ)]
    exact hoffset.add hvariable
  have hreconstruct :
      constantDifference + variableScore =
        equation.difference
          (fun index => (occurrences.get index).eval input) := by
    have hresidual :=
      occurrenceWeightedResidual_reconstruction occurrences liveScale input
        Finset.univ equation.weights
    unfold constantDifference variableScore
      LabelledEquation.difference LabelledEquation.score
    linarith
  rw [show (∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
      modularCoefficientResidue equation modulus index *
        (occurrenceResidualVariable occurrences
          (normalizedLiveSet occurrences liveScale) input index).toNat) =
      ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
        modularCoefficientResidue equation modulus index *
          (variableBit index).toNat by rfl]
  unfold LabelledEquation.HoldsModulo
  rw [← hreconstruct]
  have hemod := hcombined.eq
  rw [show
      (modularResidualOffset occurrences liveScale input equation modulus +
        ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
          modularCoefficientResidue equation modulus index *
            (variableBit index).toNat) % modulus = 0 ↔
        (((modularResidualOffset occurrences liveScale input equation modulus +
          ∑ index ∈ (Finset.univ : Finset (Fin occurrences.length)),
            modularCoefficientResidue equation modulus index *
              (variableBit index).toNat : ℕ) : ℕ) : ℤ) %
            (modulus : ℤ) = 0 by norm_cast]
  exact hemod ▸ Iff.rfl

/-- A threshold modular row built from the same canonical list coordinate used
by direct symmetric rows.  Digit positions share one walk sample and differ
only in their padded active-set mask. -/
noncomputable def canonicalOccurrenceModularRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ) : Bool :=
  modularRadixRow modulus offset base fun digit candidate =>
    canonicalOccurrenceListCoordinate occurrences liveScale denominator
      (active digit) sample candidate

theorem canonicalOccurrenceModularRadixRow_eq_of_certificate
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset base : ℕ)
    (hsucceeds : ∀ digit,
      (normalizedOccurrenceListCertificate spectrum occurrences
        liveScale denominator).succeeds (active digit) sample = true) :
    canonicalOccurrenceModularRadixRow occurrences liveScale denominator
        active sample modulus offset base =
      modularTupleAccepts modulus offset base
        (boundedActivePopulation active) := by
  unfold canonicalOccurrenceModularRadixRow
  apply modularRadixRow_eq_of_oneHot modulus offset base _
    (boundedActivePopulation active)
  intro digit candidate
  rw [compiledCanonicalOccurrenceListCoordinate_eq_of_certificate
    spectrum occurrences liveScale denominator (active digit)
      sample candidate (hsucceeds digit)]
  apply decide_eq_decide.mpr
  constructor
  · intro hvalue
    apply Fin.ext
    exact hvalue
  · intro hequal
    exact congrArg Fin.val hequal

theorem canonicalOccurrenceModularRadixRow_mismatch_le
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
    (modulus offset base : ℕ) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            occurrences liveScale denominator =>
          canonicalOccurrenceModularRadixRow occurrences liveScale denominator
              active sample modulus offset base !=
            modularTupleAccepts modulus offset base
              (boundedActivePopulation active)) ≤
      Fintype.card (Fin digits) *
        (normalizedOccurrenceListCertificate spectrum occurrences
          liveScale denominator).failure := by
  let certificate :=
    normalizedOccurrenceListCertificate spectrum occurrences
      liveScale denominator
  apply booleanMean_unionBound_uniform
    (fun sample : NormalizedOccurrenceListSeed
        occurrences liveScale denominator =>
      canonicalOccurrenceModularRadixRow occurrences liveScale denominator
          active sample modulus offset base !=
        modularTupleAccepts modulus offset base
          (boundedActivePopulation active))
    (fun digit sample => !(certificate.succeeds (active digit) sample))
    certificate.failure
  · intro sample hmismatch
    by_contra hnone
    have hall : ∀ digit,
        certificate.succeeds (active digit) sample = true := by
      intro digit
      cases hvalue : certificate.succeeds (active digit) sample
      · exfalso
        apply hnone
        exact ⟨digit, by simp [hvalue]⟩
      · rfl
    have hequal :=
      canonicalOccurrenceModularRadixRow_eq_of_certificate
        spectrum occurrences liveScale denominator active sample
          modulus offset base hall
    rw [hequal] at hmismatch
    simp at hmismatch
  · intro digit
    exact certificate.pointwise (active digit)

theorem canonicalOccurrenceModularRadixRow_mismatch_reciprocal
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ)
    (active : Fin digits →
      BoundedActiveSet occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale)))
    (modulus offset base : ℕ) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            occurrences liveScale denominator =>
          canonicalOccurrenceModularRadixRow occurrences liveScale denominator
              active sample modulus offset base !=
            modularTupleAccepts modulus offset base
              (boundedActivePopulation active)) ≤
      (digits : ℝ) / (denominator + 1 : ℕ) := by
  calc
    _ ≤ Fintype.card (Fin digits) *
        (normalizedOccurrenceListCertificate spectrum occurrences
          liveScale denominator).failure :=
      canonicalOccurrenceModularRadixRow_mismatch_le spectrum occurrences
        liveScale denominator active modulus offset base
    _ ≤ (digits : ℝ) * (1 / (denominator + 1 : ℕ)) := by
      rw [Fintype.card_fin]
      gcongr
      exact normalizedOccurrenceListFailure_le spectrum occurrences
        liveScale denominator
    _ = (digits : ℝ) / (denominator + 1 : ℕ) := by ring

/-- Threshold specialization of the generic modular row: coefficient bits are
derived from one signed equation after its coefficients have been represented
by canonical nonnegative residues. -/
noncomputable def canonicalOccurrenceCoefficientRadixRow
    {q digits : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (sample : NormalizedOccurrenceListSeed
      occurrences liveScale denominator)
    (modulus offset : ℕ) : Bool :=
  canonicalOccurrenceModularRadixRow occurrences liveScale denominator
    (fun digit : Fin digits =>
      normalizedCoefficientBitActiveSet occurrences liveScale input
        mask coefficient digit.val)
    sample modulus offset 2

theorem canonicalOccurrenceCoefficientRadixRow_mismatch_reciprocal
    {q digits : ℕ}
    (spectrum : ExpanderSpectrumContract)
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) (input : BitInput q)
    (mask : Finset (Fin occurrences.length))
    (coefficient : Fin occurrences.length → ℕ)
    (modulus offset : ℕ)
    (hcoefficient : ∀ index, coefficient index < 2 ^ digits) :
    booleanMean
        (fun sample : NormalizedOccurrenceListSeed
            occurrences liveScale denominator =>
          canonicalOccurrenceCoefficientRadixRow (digits := digits)
              occurrences liveScale
              denominator input mask coefficient sample modulus offset !=
            decide ((offset +
              ∑ index ∈ mask, coefficient index *
                (occurrenceResidualVariable occurrences
                  (normalizedLiveSet occurrences liveScale) input
                    index).toNat) % modulus = 0)) ≤
      (digits : ℝ) / (denominator + 1 : ℕ) := by
  have hbound :=
    canonicalOccurrenceModularRadixRow_mismatch_reciprocal spectrum
      occurrences liveScale denominator
      (fun digit : Fin digits =>
        normalizedCoefficientBitActiveSet occurrences liveScale input
          mask coefficient digit.val)
      modulus offset 2
  have hvalue :=
    coefficientBitRadixValue_eq occurrences liveScale input
      mask coefficient hcoefficient
  simpa [canonicalOccurrenceCoefficientRadixRow,
    modularTupleAccepts, hvalue] using hbound

def modulusDigitCount (modulus : ℕ) : ℕ :=
  (Nat.log 2 modulus).succ

/-- Finite Fubini bound with explicit cardinality hypotheses, so callers can
use certificate-provided nonemptiness without installing global instances. -/
theorem booleanMean_product_le_of_fiber
    {Left Right : Type} [Fintype Left] [Fintype Right]
    (event : Left × Right → Bool) (bound : ℝ)
    (hleft : 0 < Fintype.card Left)
    (hright : 0 < Fintype.card Right)
    (hfiber : ∀ left,
      booleanMean (fun right => event (left, right)) ≤ bound) :
    booleanMean event ≤ bound := by
  have hleftReal : (0 : ℝ) < Fintype.card Left := by exact_mod_cast hleft
  have hrightReal : (0 : ℝ) < Fintype.card Right := by
    exact_mod_cast hright
  have hproductReal :
      (0 : ℝ) < Fintype.card Left * Fintype.card Right := by positivity
  have hsum : ∀ left,
      (∑ right, bitAsReal (event (left, right))) ≤
        Fintype.card Right * bound := by
    intro left
    simpa [mul_comm] using (div_le_iff₀ hrightReal).mp (hfiber left)
  unfold booleanMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  calc
    (∑ left, ∑ right, bitAsReal (event (left, right))) /
          (Fintype.card Left * Fintype.card Right : ℕ) ≤
        (∑ _left : Left, Fintype.card Right * bound) /
          (Fintype.card Left * Fintype.card Right : ℕ) := by
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum fun left _ => hsum left
      · positivity
    _ = bound := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      push_cast
      field_simp

theorem booleanMean_product_left
    {Left Right : Type} [Fintype Left] [Fintype Right]
    (event : Left → Bool)
    (hleft : 0 < Fintype.card Left)
    (hright : 0 < Fintype.card Right) :
    booleanMean (fun sample : Left × Right => event sample.1) =
      booleanMean event := by
  have hleftReal : (0 : ℝ) < Fintype.card Left := by exact_mod_cast hleft
  have hrightReal : (0 : ℝ) < Fintype.card Right := by
    exact_mod_cast hright
  unfold booleanMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  field_simp

theorem booleanMean_mismatch_triangle
    {Sample : Type} [Fintype Sample]
    (left middle right : Sample → Bool) :
    booleanMean (fun sample => left sample != right sample) ≤
      booleanMean (fun sample => left sample != middle sample) +
        booleanMean (fun sample => middle sample != right sample) := by
  unfold booleanMean
  rw [← add_div]
  gcongr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro sample _
  cases hleft : left sample <;>
    cases hmiddle : middle sample <;>
    cases hright : right sample <;>
    norm_num [bitAsReal, hleft, hmiddle, hright]

/-! ## One row-aggregation path -/

/-- A finite row system.  `row` is deliberately Boolean even away from the
legal-list event, matching the total-row discipline in (A.13.7). -/
structure FiniteRowAggregation (Input Row : Type) [Fintype Input] [Fintype Row]
    where
  row : Row → Input → Bool

def FiniteRowAggregation.acceptanceCount
    {Input Row : Type} [Fintype Input] [Fintype Row]
    (aggregation : FiniteRowAggregation Input Row) : ℕ :=
  ∑ row, ∑ input, (aggregation.row row input).toNat

def FiniteRowAggregation.sampleCount
    (Input Row : Type) [Fintype Input] [Fintype Row] : ℕ :=
  Fintype.card Row * Fintype.card Input

noncomputable def FiniteRowAggregation.mean
    {Input Row : Type} [Fintype Input] [Fintype Row]
    (aggregation : FiniteRowAggregation Input Row) : ℝ :=
  (aggregation.acceptanceCount : ℝ) /
    FiniteRowAggregation.sampleCount Input Row

def FiniteRowAggregation.outputCode
    {Input Row : Type} [Fintype Input] [Fintype Row]
    (aggregation : FiniteRowAggregation Input Row) : ℕ :=
  encodeNaturalRatio aggregation.acceptanceCount
    (FiniteRowAggregation.sampleCount Input Row - 1)

theorem FiniteRowAggregation.sampleCount_pos
    (Input Row : Type) [Fintype Input] [Fintype Row]
    [Nonempty Input] [Nonempty Row] :
    0 < FiniteRowAggregation.sampleCount Input Row := by
  exact Nat.mul_pos Fintype.card_pos Fintype.card_pos

theorem FiniteRowAggregation.decode_outputCode
    {Input Row : Type} [Fintype Input] [Fintype Row]
    [Nonempty Input] [Nonempty Row]
    (aggregation : FiniteRowAggregation Input Row) :
    decodeSupplierRational aggregation.outputCode =
      (aggregation.acceptanceCount : ℚ) /
        FiniteRowAggregation.sampleCount Input Row := by
  rw [FiniteRowAggregation.outputCode,
    decodeSupplierRational_encodeNaturalRatio]
  congr 1
  exact_mod_cast Nat.sub_add_cancel
    (Nat.succ_le_iff.mpr
      (FiniteRowAggregation.sampleCount_pos Input Row))

theorem bitAsReal_sub_abs_eq_mismatch (left right : Bool) :
    |bitAsReal left - bitAsReal right| = bitAsReal (left != right) := by
  cases left <;> cases right <;> norm_num [bitAsReal]

theorem FiniteRowAggregation.acceptanceCount_cast
    {Input Row : Type} [Fintype Input] [Fintype Row]
    (aggregation : FiniteRowAggregation Input Row) :
    (aggregation.acceptanceCount : ℝ) =
      ∑ row, ∑ input, bitAsReal (aggregation.row row input) := by
  unfold FiniteRowAggregation.acceptanceCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases aggregation.row row input <;> simp [bitAsReal]

theorem FiniteRowAggregation.mean_eq_product_mean
    {Input Row : Type} [Fintype Input] [Fintype Row]
    (aggregation : FiniteRowAggregation Input Row) :
    aggregation.mean =
      booleanMean (fun sample : Row × Input =>
        aggregation.row sample.1 sample.2) := by
  unfold FiniteRowAggregation.mean booleanMean
  rw [FiniteRowAggregation.acceptanceCount_cast]
  rw [Fintype.card_prod]
  unfold FiniteRowAggregation.sampleCount
  congr 1
  rw [Fintype.sum_prod_type]

theorem FiniteRowAggregation.decode_outputCode_cast
    {Input Row : Type} [Fintype Input] [Fintype Row]
    [Nonempty Input] [Nonempty Row]
    (aggregation : FiniteRowAggregation Input Row) :
    (decodeSupplierRational aggregation.outputCode : ℝ) =
      aggregation.mean := by
  rw [FiniteRowAggregation.decode_outputCode, Rat.cast_div,
    Rat.cast_natCast]
  rfl

theorem card_bitInput (q : ℕ) :
    Fintype.card (BitInput q) = 2 ^ q := by
  rw [Fintype.card_fun]
  simp

/-- Finite Fubini/union step used by both (A.13.9) and (A.13.10).  Correctness
is pointwise in the input; it never assumes one row works for every input. -/
theorem FiniteRowAggregation.error_le_of_pointwise
    {Input Row : Type} [Fintype Input] [Fintype Row]
    [Nonempty Input] [Nonempty Row]
    (aggregation : FiniteRowAggregation Input Row)
    (target : Input → Bool) (failure : ℝ)
    (hpointwise : ∀ input,
      booleanMean (fun row => aggregation.row row input != target input) ≤
        failure) :
    |aggregation.mean - booleanMean target| ≤ failure := by
  have hrowCard : (0 : ℝ) < Fintype.card Row := by
    exact_mod_cast Fintype.card_pos
  have hinputCard : (0 : ℝ) < Fintype.card Input := by
    exact_mod_cast Fintype.card_pos
  have hproductCard :
      (0 : ℝ) < (Fintype.card Row * Fintype.card Input : ℕ) := by
    exact_mod_cast Nat.mul_pos Fintype.card_pos Fintype.card_pos
  have hrow : ∀ input,
      (∑ row, |bitAsReal (aggregation.row row input) -
          bitAsReal (target input)|) ≤
        Fintype.card Row * failure := by
    intro input
    calc
      (∑ row, |bitAsReal (aggregation.row row input) -
          bitAsReal (target input)|) =
          ∑ row, bitAsReal
            (aggregation.row row input != target input) := by
              apply Finset.sum_congr rfl
              intro row _
              exact bitAsReal_sub_abs_eq_mismatch _ _
      _ ≤ Fintype.card Row * failure := by
        have hscaled := (div_le_iff₀ hrowCard).mp
          (hpointwise input)
        simpa [booleanMean, mul_comm] using hscaled
  have hnormalize :
      booleanMean target =
        (Fintype.card Row * ∑ input, bitAsReal (target input)) /
          (Fintype.card Row * Fintype.card Input : ℕ) := by
    unfold booleanMean
    push_cast
    field_simp
  rw [FiniteRowAggregation.mean_eq_product_mean, hnormalize]
  unfold booleanMean
  rw [Fintype.card_prod]
  have hnumerator :
      |(∑ sample : Row × Input,
          bitAsReal (aggregation.row sample.1 sample.2)) -
          Fintype.card Row * ∑ input, bitAsReal (target input)| ≤
            Fintype.card Input * (Fintype.card Row * failure) := by
    rw [Fintype.sum_prod_type_right]
    have hreplicate :
        Fintype.card Row * ∑ input, bitAsReal (target input) =
          ∑ input, ∑ _row : Row, bitAsReal (target input) := by
      simp [mul_sum]
    rw [hreplicate, ← Finset.sum_sub_distrib]
    calc
      |∑ input, (∑ row, bitAsReal (aggregation.row row input) -
          ∑ _row : Row, bitAsReal (target input))| ≤
          ∑ input, |(∑ row, bitAsReal (aggregation.row row input)) -
            ∑ _row : Row, bitAsReal (target input)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ input, ∑ row,
          |bitAsReal (aggregation.row row input) -
            bitAsReal (target input)| := by
        apply Finset.sum_le_sum
        intro input _
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _input : Input, Fintype.card Row * failure :=
        Finset.sum_le_sum fun input _ => hrow input
      _ = Fintype.card Input * (Fintype.card Row * failure) := by simp
  rw [← sub_div]
  rw [abs_div, abs_of_pos hproductCard]
  apply (div_le_iff₀ hproductCard).2
  calc
    |(∑ sample : Row × Input,
        bitAsReal (aggregation.row sample.1 sample.2)) -
      Fintype.card Row * ∑ input, bitAsReal (target input)| ≤
        Fintype.card Input * (Fintype.card Row * failure) :=
      hnumerator
    _ = (Fintype.card Row * Fintype.card Input : ℕ) * failure := by
      push_cast
      ring
    _ = failure *
        (Fintype.card Row * Fintype.card Input : ℕ) := by ring

/-! ## Request preprocessing and the sole production estimate -/

/-- Both circuit modes preprocess to the same object: a nonempty, explicitly
enumerated family of total Boolean rows.  A natural row count keeps the
preprocessor executable and avoids a second abstract finite-index path. -/
structure FourfoldRowPreprocessor
    (Circuit : CircuitFamily)
    (evaluate : {q : ℕ} → Circuit q → BitInput q → Bool) where
  rowCount : FourfoldRequest Circuit → ℕ
  rowCountPositive : ∀ request, 0 < rowCount request
  row : (request : FourfoldRequest Circuit) →
    Fin (rowCount request) → BitInput request.q → Bool
  failure : FourfoldRequest Circuit → ℝ
  failureNonnegative : ∀ request, 0 ≤ failure request
  pointwise : ∀ request input,
    booleanMean (fun index => row request index input !=
      conjunctionBit evaluate request.circuits input) ≤ failure request

def FourfoldRowPreprocessor.aggregation
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) :
    FiniteRowAggregation (BitInput request.q)
      (Fin (preprocessor.rowCount request)) where
  row := preprocessor.row request

instance FourfoldRowPreprocessor.rowNonempty
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) :
    Nonempty (Fin (preprocessor.rowCount request)) :=
  ⟨⟨0, preprocessor.rowCountPositive request⟩⟩

def FourfoldRowPreprocessor.outputCode
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) : ℕ :=
  (preprocessor.aggregation request).outputCode

noncomputable def FourfoldRowPreprocessor.estimate
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) : ℝ :=
  (preprocessor.aggregation request).mean

theorem FourfoldRowPreprocessor.decode_outputCode
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) :
    (decodeSupplierRational (preprocessor.outputCode request) : ℝ) =
      preprocessor.estimate request := by
  exact (preprocessor.aggregation request).decode_outputCode_cast

theorem FourfoldRowPreprocessor.accurate
    {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (preprocessor : FourfoldRowPreprocessor Circuit evaluate)
    (request : FourfoldRequest Circuit) :
    |preprocessor.estimate request -
        conjunctionProbability evaluate request.circuits| ≤
      preprocessor.failure request := by
  exact (preprocessor.aggregation request).error_le_of_pointwise
    (fun input => conjunctionBit evaluate request.circuits input)
    (preprocessor.failure request) (preprocessor.pointwise request)

/-! ## Closed componentwise error ledger -/

/-- One denominator simultaneously reserves a factor of two for prime/list
error and a factor equal to the number of externally summed rows. -/
def reciprocalUnionDenominator
    (familySize targetDenominator : ℕ) : ℕ :=
  2 * familySize * (targetDenominator + 1)

theorem reciprocalUnionBudget
    (familySize targetDenominator : ℕ) :
    (familySize : ℝ) *
        (1 / (reciprocalUnionDenominator
            familySize targetDenominator + 1 : ℕ) +
          1 / (reciprocalUnionDenominator
            familySize targetDenominator + 1 : ℕ)) ≤
      1 / (targetDenominator + 1 : ℕ) := by
  let budget :=
    reciprocalUnionDenominator familySize targetDenominator + 1
  have hbudgetPositive : (0 : ℝ) < (budget : ℕ) := by
    exact_mod_cast Nat.succ_pos
      (reciprocalUnionDenominator familySize targetDenominator)
  have htargetPositive :
      (0 : ℝ) < (targetDenominator + 1 : ℕ) := by positivity
  rw [show (familySize : ℝ) *
      (1 / (budget : ℕ) + 1 / (budget : ℕ)) =
        (2 * familySize : ℝ) / budget by ring]
  rw [div_le_div_iff₀ hbudgetPositive htargetPositive]
  dsimp [budget]
  unfold reciprocalUnionDenominator
  push_cast
  nlinarith

theorem twoComponentUnionError_le
    (familySize targetDenominator : ℕ)
    (primeError listError : ℝ)
    (hprime : primeError ≤
      1 / (reciprocalUnionDenominator
          familySize targetDenominator + 1 : ℕ))
    (hlist : listError ≤
      1 / (reciprocalUnionDenominator
          familySize targetDenominator + 1 : ℕ)) :
    (familySize : ℝ) * (primeError + listError) ≤
      1 / (targetDenominator + 1 : ℕ) := by
  calc
    (familySize : ℝ) * (primeError + listError) ≤
        (familySize : ℝ) *
          (1 / (reciprocalUnionDenominator
              familySize targetDenominator + 1 : ℕ) +
            1 / (reciprocalUnionDenominator
              familySize targetDenominator + 1 : ℕ)) := by
      gcongr
    _ ≤ 1 / (targetDenominator + 1 : ℕ) :=
      reciprocalUnionBudget familySize targetDenominator

/-! ## Concrete row preprocessors -/

theorem booleanMean_equivFin
    (Index : Type) [Fintype Index]
    (enumeration : Index ≃ Fin (Fintype.card Index))
    (value : Index → Bool) :
    booleanMean (fun index => value (enumeration.symm index)) =
      booleanMean value := by
  unfold booleanMean
  rw [Equiv.sum_comp enumeration.symm
    (fun index => bitAsReal (value index))]
  simp

/-- The canonical powered-walk seed has an explicit mixed-radix index. -/
def normalizedOccurrenceListSeedFinEquiv {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    NormalizedOccurrenceListSeed occurrences liveScale denominator ≃
      Fin
        (Fintype.card
          (NormalizedOccurrenceListSeed occurrences liveScale denominator)) :=
  canonicalWalkSampleFinEquiv
    (2 ^ toeplitzWalkSideBits
      (canonicalGradedRank occurrences.length
        (touchingCost (occurrenceSupport occurrences)
          (normalizedLiveSet occurrences liveScale))))
    denominator

/-- Primes are enumerated increasingly; no arbitrary finite equivalence is
used by the threshold row compiler. -/
def primeIndexFinEquiv (cutoff : ℕ) :
    PrimeIndex cutoff ≃ Fin (Fintype.card (PrimeIndex cutoff)) :=
  (Fintype.orderIsoFinOfCardEq (PrimeIndex cutoff) rfl).symm.toEquiv

/-- Mixed-radix index for the one shared prime/list sample. -/
def primeListSampleFinEquiv {q cutoff : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (liveScale denominator : ℕ) :
    (PrimeIndex cutoff ×
      NormalizedOccurrenceListSeed occurrences liveScale denominator) ≃
      Fin
        (Fintype.card
          (PrimeIndex cutoff ×
            NormalizedOccurrenceListSeed occurrences liveScale
              denominator)) :=
  ((Equiv.prodCongr
      (primeIndexFinEquiv cutoff)
      (normalizedOccurrenceListSeedFinEquiv occurrences liveScale
        denominator)).trans
    finProdFinEquiv).trans
      (finCongr (Fintype.card_prod _ _).symm)

/-- One denominator pays for every circuit in the symmetric request.  The
extra successor in the actual sample denominator makes this valid even for an
empty request, without a special row path. -/
def symmetricListDenominator
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (targetDenominator : ℕ) : ℕ :=
  request.circuits.length * (targetDenominator + 1)

theorem symmetricListError_le
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (targetDenominator : ℕ) :
    (request.circuits.length : ℝ) /
        (symmetricListDenominator request targetDenominator + 1 : ℕ) ≤
      1 / (targetDenominator + 1 : ℕ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  unfold symmetricListDenominator
  push_cast
  nlinarith

/-- The production symmetric rows with all list-error parameters chosen from
the requested reciprocal accuracy. -/
noncomputable def symmetricFourfoldRows
    (spectrum : ExpanderSpectrumContract)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ) :
    FourfoldRowPreprocessor NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.eval where
  rowCount request :=
    Fintype.card
      (NormalizedOccurrenceListSeed
        (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (targetDenominator request.q)))
  rowCountPositive request :=
    (normalizedOccurrenceListCertificate spectrum
      (symmetricFourfoldOccurrences request) liveScale
        (symmetricListDenominator request
          (targetDenominator request.q))).cardPositive
  row request index input :=
    canonicalSymmetricFourfoldRow request liveScale
      (symmetricListDenominator request (targetDenominator request.q)) input
      ((normalizedOccurrenceListSeedFinEquiv
        (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (targetDenominator request.q))).symm index)
  failure request := 1 / (targetDenominator request.q + 1 : ℕ)
  failureNonnegative _ := by positivity
  pointwise request input := by
    let Sample :=
      NormalizedOccurrenceListSeed
        (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request
            (targetDenominator request.q))
    let value : Sample → Bool := fun sample =>
      canonicalSymmetricFourfoldRow request liveScale
          (symmetricListDenominator request
            (targetDenominator request.q))
          input sample !=
        conjunctionBit NormalizedSymmetricThresholdCircuit.eval
          request.circuits input
    change
      booleanMean
          (fun index : Fin (Fintype.card Sample) =>
            value
              ((normalizedOccurrenceListSeedFinEquiv
                (symmetricFourfoldOccurrences request) liveScale
                  (symmetricListDenominator request
                    (targetDenominator request.q))).symm index)) ≤
        1 / (targetDenominator request.q + 1 : ℕ)
    calc
      _ = booleanMean value :=
        booleanMean_equivFin Sample
          (normalizedOccurrenceListSeedFinEquiv
            (symmetricFourfoldOccurrences request) liveScale
              (symmetricListDenominator request
                (targetDenominator request.q)))
          value
      _ ≤ request.circuits.length /
          (symmetricListDenominator request
            (targetDenominator request.q) + 1 : ℕ) :=
        canonicalSymmetricFourfoldRow_mismatch_reciprocal spectrum request
          liveScale
          (symmetricListDenominator request (targetDenominator request.q))
          input
      _ ≤ 1 / (targetDenominator request.q + 1 : ℕ) :=
        symmetricListError_le request (targetDenominator request.q)

/-! ## One fixed raw-request program for both normalized modes -/

end NearCubicWires.SupplierEstimator
