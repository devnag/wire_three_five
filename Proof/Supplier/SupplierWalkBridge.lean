import Proof.Supplier.SupplierListSchedule
import Proof.Supplier.SupplierWalk

/-!
# Toeplitz-list amplification on the powered Margulis walk

The production list uses a `3 * rank - 1`-bit Toeplitz seed, whereas the
Margulis graph has a square vertex set.  We embed the seed set in the smallest
square binary vertex set and ignore its (at most one) padding bit.  The
cardinality calculation below proves that this fixed relabeling preserves the
uniform bad-seed density exactly before applying the powered-walk theorem.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierWalkBridge

open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk

/-- Number of binary coordinates in the canonical Toeplitz seed. -/
def toeplitzSeedBits (rank : ℕ) : ℕ :=
  2 * rank + (rank - 1)

/-- A Toeplitz seed uses fewer than three copies of the rank width. -/
theorem toeplitzSeedBits_le_three_mul (rank : ℕ) :
    toeplitzSeedBits rank ≤ 3 * rank := by
  unfold toeplitzSeedBits
  omega

/-- Side-bit width of the smallest square binary vertex set containing every
Toeplitz seed. -/
def toeplitzWalkSideBits (rank : ℕ) : ℕ :=
  (toeplitzSeedBits rank + 1) / 2

/-- Squaring the padded walk side adds at most one padding bit. -/
theorem twice_toeplitzWalkSideBits_le (rank : ℕ) :
    2 * toeplitzWalkSideBits rank ≤ toeplitzSeedBits rank + 1 := by
  unfold toeplitzWalkSideBits
  omega

/-- The square seed space has zero or one coordinate beyond the Toeplitz seed.
Keeping the padding as a type makes the density-preservation proof exact. -/
abbrev ToeplitzWalkPadding (rank : ℕ) :=
  Fin (2 ^ (2 * toeplitzWalkSideBits rank - toeplitzSeedBits rank))

theorem toeplitzSeedBits_le_twice_sideBits (rank : ℕ) :
    toeplitzSeedBits rank ≤ 2 * toeplitzWalkSideBits rank := by
  unfold toeplitzWalkSideBits
  omega

theorem card_margulisVertex_toeplitzWalkSide (rank : ℕ) :
    Fintype.card
        (MargulisVertex (2 ^ toeplitzWalkSideBits rank)) =
      Fintype.card
        (ToeplitzSeed rank × ToeplitzWalkPadding rank) := by
  have hbits := toeplitzSeedBits_le_twice_sideBits rank
  calc
    Fintype.card
        (MargulisVertex (2 ^ toeplitzWalkSideBits rank)) =
        2 ^ toeplitzWalkSideBits rank *
          2 ^ toeplitzWalkSideBits rank := by
      simp [MargulisVertex, ZMod.card]
    _ = 2 ^ (2 * toeplitzWalkSideBits rank) := by
      rw [← pow_add]
      congr 1
      omega
    _ = 2 ^ toeplitzSeedBits rank *
        2 ^ (2 * toeplitzWalkSideBits rank -
          toeplitzSeedBits rank) := by
      rw [← pow_add]
      congr 1
      omega
    _ = Fintype.card (ToeplitzSeed rank) *
        Fintype.card (ToeplitzWalkPadding rank) := by
      rw [card_toeplitzSeed]
      simp only [Fintype.card_fin]
      unfold toeplitzSeedBits
      rfl
    _ = Fintype.card
        (ToeplitzSeed rank × ToeplitzWalkPadding rank) := by
      exact (Fintype.card_prod
        (ToeplitzSeed rank) (ToeplitzWalkPadding rank)).symm

/-- Split one bit vector into the lower diagonals, upper diagonals, and
translation used by a Toeplitz seed.  This explicit equivalence replaces an
arbitrary finite-cardinality choice at the executable boundary. -/
def toeplitzSeedBitEquiv (rank : ℕ) :
    (Fin (toeplitzSeedBits rank) → SupplierToeplitzCore.𝔽₂) ≃
      ToeplitzSeed rank where
  toFun bits :=
    ⟨⟨(fun index : Fin rank => bits ⟨index.val, by
          unfold toeplitzSeedBits
          omega⟩),
        fun index : Fin (rank - 1) => bits ⟨rank + index.val, by
          unfold toeplitzSeedBits
          omega⟩⟩,
      fun index : Fin rank => bits ⟨rank + (rank - 1) + index.val, by
          unfold toeplitzSeedBits
          omega⟩⟩
  invFun seed := fun index =>
    if hmain : index.val < rank then
      seed.1.1 ⟨index.val, hmain⟩
    else if hupper : index.val < rank + (rank - 1) then
      seed.1.2 ⟨index.val - rank, by omega⟩
    else
      seed.2 ⟨index.val - (rank + (rank - 1)), by
        have := index.isLt
        unfold toeplitzSeedBits at this
        omega⟩
  left_inv bits := by
    funext index
    simp only
    split
    · rfl
    · split
      · congr 1
        apply Fin.ext
        change rank + (index.val - rank) = index.val
        omega
      · congr 1
        apply Fin.ext
        have := index.isLt
        unfold toeplitzSeedBits at this
        change
          rank + (rank - 1) +
              (index.val - (rank + (rank - 1))) =
            index.val
        omega
  right_inv seed := by
    rcases seed with ⟨⟨main, upper⟩, translation⟩
    apply Prod.ext
    · change
        ((fun index : Fin rank =>
            if hmain : index.val < rank then
              main ⟨index.val, hmain⟩
            else
              if hupper : index.val < rank + (rank - 1) then
                upper ⟨index.val - rank, by omega⟩
              else
                translation
                  ⟨index.val - (rank + (rank - 1)), by omega⟩),
          (fun index : Fin (rank - 1) =>
            if hmain : rank + index.val < rank then
              main ⟨rank + index.val, hmain⟩
            else
              if hupper : rank + index.val < rank + (rank - 1) then
                upper ⟨rank + index.val - rank, by omega⟩
              else
                translation
                  ⟨rank + index.val - (rank + (rank - 1)), by omega⟩)) =
          (main, upper)
      apply Prod.ext
      · funext index
        simp
      · funext index
        simp only
        rw [dif_neg (by omega), dif_pos (by
          have := index.isLt
          omega)]
        congr 1
        apply Fin.ext
        change rank + index.val - rank = index.val
        omega
    · change
        (fun index : Fin rank =>
          if hmain : rank + (rank - 1) + index.val < rank then
            main ⟨rank + (rank - 1) + index.val, hmain⟩
          else if hupper :
              rank + (rank - 1) + index.val <
                rank + (rank - 1) then
            upper
              ⟨rank + (rank - 1) + index.val - rank, by omega⟩
          else
            translation
              ⟨rank + (rank - 1) + index.val -
                (rank + (rank - 1)), by omega⟩) =
          translation
      funext index
      rw [dif_neg (by omega), dif_neg (by omega)]
      congr 1
      apply Fin.ext
      have := index.isLt
      change
        rank + (rank - 1) + index.val -
            (rank + (rank - 1)) =
          index.val
      omega

/-- Binary functions are enumerated by their ordinary low-to-high bit code. -/
def binaryFunctionFinEquiv (bits : ℕ) :
    (Fin bits → SupplierToeplitzCore.𝔽₂) ≃ Fin (2 ^ bits) :=
  (Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).symm).trans
    finFunctionFinEquiv

/-- The walk start vertex is decoded into the Toeplitz seed and its unused
zero-or-one padding bit by a concrete binary bijection.  Every component is
computable, so the production row no longer hides a choice-derived relabeling. -/
def toeplitzWalkEncoding (rank : ℕ) :
    MargulisVertex (2 ^ toeplitzWalkSideBits rank) ≃
      ToeplitzSeed rank × ToeplitzWalkPadding rank := by
  let side := toeplitzWalkSideBits rank
  let bits := toeplitzSeedBits rank
  let padding := 2 * side - bits
  have hbits : bits ≤ 2 * side :=
    toeplitzSeedBits_le_twice_sideBits rank
  have hsquare :
      2 ^ side * 2 ^ side = 2 ^ (2 * side) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit :
      2 ^ bits * 2 ^ padding = 2 ^ (2 * side) := by
    rw [← pow_add]
    congr 1
    dsimp [padding]
    omega
  exact
    ((Equiv.prodCongr
        (ZMod.finEquiv (2 ^ side)).symm.toEquiv
        (ZMod.finEquiv (2 ^ side)).symm.toEquiv).trans
      finProdFinEquiv).trans <|
    (finCongr hsquare).trans <|
    ((finProdFinEquiv.trans (finCongr hsplit)).symm.trans <|
      Equiv.prodCongr
        ((binaryFunctionFinEquiv bits).symm.trans <|
          toeplitzSeedBitEquiv rank)
        (Equiv.refl (Fin (2 ^ padding))))

/-! ## Executable walk-sample enumeration -/

/-- The ordinary residue representatives enumerate a Margulis vertex without
choice. -/
def margulisVertexFinEquiv (m : ℕ) [NeZero m] :
    MargulisVertex m ≃ Fin (Fintype.card (MargulisVertex m)) := by
  have hcard :
      m * m = Fintype.card (MargulisVertex m) := by
    simp [MargulisVertex, ZMod.card]
  exact
    ((Equiv.prodCongr
        (ZMod.finEquiv m).symm.toEquiv
        (ZMod.finEquiv m).symm.toEquiv).trans
      finProdFinEquiv).trans (finCongr hcard)

/-- Forty base labels are encoded as one base-16 natural. -/
def poweredMargulisLabelFinEquiv :
    PoweredMargulisLabel ≃ Fin (Fintype.card PoweredMargulisLabel) := by
  exact finFunctionFinEquiv.trans
    (finCongr card_poweredMargulisLabel.symm)

def poweredMargulisLabelsFinEquiv (n : ℕ) :
    (Fin n → PoweredMargulisLabel) ≃
      Fin (Fintype.card PoweredMargulisLabel ^ n) :=
  (Equiv.piCongrRight fun _ => poweredMargulisLabelFinEquiv).trans
    finFunctionFinEquiv

/-- A positive-length walk sample has a fixed mixed-radix enumeration:
first its start vertex, then every powered transition label. -/
def positiveWalkSampleFinEquiv (m n : ℕ) [NeZero m] :
    MargulisWalkSample m n.succ ≃
      Fin (Fintype.card (MargulisWalkSample m n.succ)) := by
  have hcard :
      Fintype.card (MargulisVertex m) *
          Fintype.card PoweredMargulisLabel ^ n =
        Fintype.card (MargulisWalkSample m n.succ) :=
    (card_positiveSample (m := m) (n := n)).symm
  exact
    (positiveSampleEquiv.trans <|
      (Equiv.prodCongr
        (margulisVertexFinEquiv m)
        (poweredMargulisLabelsFinEquiv n)).trans
          finProdFinEquiv).trans
      (finCongr hcard)

theorem booleanMean_toeplitzWalkEncoding
    (rank : ℕ) (bad : ToeplitzSeed rank → Bool) :
    booleanMean (fun vertex :
        MargulisVertex (2 ^ toeplitzWalkSideBits rank) =>
      bad (toeplitzWalkEncoding rank vertex).1) =
      booleanMean bad := by
  unfold booleanMean
  rw [Equiv.sum_comp (toeplitzWalkEncoding rank)
    (fun encoded => bitAsReal (bad encoded.1))]
  rw [card_margulisVertex_toeplitzWalkSide]
  rw [Fintype.card_prod]
  push_cast
  change
    (∑ encoded : ToeplitzSeed rank × ToeplitzWalkPadding rank,
        bitAsReal (bad encoded.1)) /
        (Fintype.card (ToeplitzSeed rank) *
          Fintype.card (ToeplitzWalkPadding rank)) =
      (∑ seed : ToeplitzSeed rank, bitAsReal (bad seed)) /
        Fintype.card (ToeplitzSeed rank)
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hpadding :
      (Fintype.card (ToeplitzWalkPadding rank) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hseed : (Fintype.card (ToeplitzSeed rank) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp [mul_comm]

/-- Evaluate the canonical Toeplitz list after decoding one walk vertex.
Padding is deliberately ignored; the preceding theorem proves this does not
change the base failure probability. -/
noncomputable def toeplitzVertexSucceeds
    {rank depth population activeBound : ℕ}
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (input : BoundedActiveSet population activeBound)
    (vertex : MargulisVertex (2 ^ toeplitzWalkSideBits rank)) : Bool :=
  polynomialListSucceeds input.1 label window terminalWindow
    (toeplitzWalkEncoding rank vertex).1

theorem toeplitzVertexFailure_eq
    {rank depth population activeBound : ℕ}
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (input : BoundedActiveSet population activeBound) :
    booleanMean (fun vertex :
        MargulisVertex (2 ^ toeplitzWalkSideBits rank) =>
      !(toeplitzVertexSucceeds label window terminalWindow input vertex)) =
      booleanMean (fun seed : ToeplitzSeed rank =>
        !(polynomialListSucceeds input.1 label
          window terminalWindow seed)) := by
  exact booleanMean_toeplitzWalkEncoding rank
    (fun seed => !(polynomialListSucceeds input.1 label
      window terminalWindow seed))

/-- The production Toeplitz list amplified by the already-verified fortieth
power Margulis walk.  The sole numeric premise is discharged by the concrete
window schedule below; keeping it explicit here separates density transport
from concentration arithmetic. -/
noncomputable def toeplitzPoweredWalkListCertificate
    (spectrum : ExpanderSpectrumContract)
    {rank depth population activeBound t : ℕ}
    (ht : Odd t)
    (hdepth : depth ≤ rank)
    (label : Fin population → BinaryVector rank)
    (hlabel : Function.Injective label)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (hwindow : ∀ level, 0 < window level)
    (hbase :
      listFailureBound activeBound window terminalWindow ≤
        (1 : ℝ) / 128) :
    AmplifiedListCertificate
      (BoundedActiveSet population activeBound)
      (MargulisWalkSample
        (2 ^ toeplitzWalkSideBits rank) t) := by
  letI : NeZero (2 ^ toeplitzWalkSideBits rank) :=
    ⟨pow_ne_zero _ (by omega)⟩
  apply concretePoweredWalkListCertificate spectrum ht
    (toeplitzVertexSucceeds label window terminalWindow)
  intro input
  rw [toeplitzVertexFailure_eq]
  exact (polynomialListFailure_bound hdepth input.1 label
    activeBound window terminalWindow
    (fun left _ right _ hne => hlabel.ne hne)
    input.2 hwindow).trans hbase

/-- Fully instantiated A.10--A.11 list certificate.  The only remaining
numeric premise is the terminal sparsity requirement; the graded windows,
their positivity, and the `1 / 128` base bound are discharged internally. -/
noncomputable def gradedToeplitzPoweredWalkListCertificate
    (spectrum : ExpanderSpectrumContract)
    {rank depth population activeBound t : ℕ}
    (ht : Odd t)
    (hdepth : depth ≤ rank)
    (hterminal : 256 * activeBound ≤ 2 ^ depth)
    (label : Fin population → BinaryVector rank)
    (hlabel : Function.Injective label) :
    AmplifiedListCertificate
      (BoundedActiveSet population activeBound)
      (MargulisWalkSample
        (2 ^ toeplitzWalkSideBits rank) t) :=
    toeplitzPoweredWalkListCertificate spectrum ht hdepth label hlabel
      (gradedWindow activeBound) gradedTerminalWindow
      (gradedWindow_pos activeBound)
      (gradedFailureBound_le activeBound depth hterminal)

/-! ## Canonical parameter closure -/

/-- A ceiling base-two logarithm expands to at most twice its positive
argument.  Keeping this arithmetic lemma local makes every later structural
enumeration bound independent of implementation details of `Nat.clog`. -/
theorem two_pow_clog_two_le_two_mul (value : ℕ) (hvalue : 0 < value) :
    2 ^ Nat.clog 2 value ≤ 2 * value := by
  by_cases hone : value = 1
  · subst value
    norm_num [Nat.clog_one_right]
  · have hvalueTwo : 1 < value := by omega
    have hpower :
        2 ^ (Nat.clog 2 value - 1) < value :=
      Nat.pow_pred_clog_lt_self (by omega) hvalueTwo
    have hclog : 0 < Nat.clog 2 value :=
      Nat.clog_pos (by omega) hvalueTwo
    conv_lhs => rw [show Nat.clog 2 value =
      (Nat.clog 2 value - 1) + 1 by omega]
    rw [Nat.pow_succ]
    omega

/-- Smallest binary depth that discharges the terminal `1 / 128` sparsity
condition. -/
def canonicalGradedDepth (activeBound : ℕ) : ℕ :=
  Nat.clog 2 (256 * activeBound)

/-- One rank simultaneously large enough for terminal sparsity and an
occurrence-sensitive injective population label. -/
def canonicalGradedRank (population activeBound : ℕ) : ℕ :=
  max (canonicalGradedDepth activeBound) (Nat.clog 2 population)

theorem canonicalGradedDepth_le_rank (population activeBound : ℕ) :
    canonicalGradedDepth activeBound ≤
      canonicalGradedRank population activeBound := by
  exact le_max_left _ _

theorem canonicalGraded_terminal (activeBound : ℕ) :
    256 * activeBound ≤ 2 ^ canonicalGradedDepth activeBound := by
  exact Nat.le_pow_clog (by omega) _

theorem population_le_two_pow_canonicalGradedRank
    (population activeBound : ℕ) :
    population ≤ 2 ^ canonicalGradedRank population activeBound := by
  exact (Nat.le_pow_clog (by omega) population).trans
    (Nat.pow_le_pow_right (by omega)
      (le_max_right (canonicalGradedDepth activeBound)
        (Nat.clog 2 population)))

/-- Canonical low-to-high binary encoding of an occurrence index.  The rank
bound proves injectivity, so row execution uses no choice-derived embedding. -/
def canonicalGradedLabel
    (population activeBound : ℕ) :
    Fin population ↪
      BinaryVector (canonicalGradedRank population activeBound) where
  toFun index := fun bit =>
    if index.val.testBit bit.val then 1 else 0
  inj' := by
    intro left right hequal
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro bit
    let rank := canonicalGradedRank population activeBound
    by_cases hbit : bit < rank
    · have hcoordinate := congrFun hequal ⟨bit, hbit⟩
      change
        (if left.val.testBit bit then (1 : ZMod 2) else 0) =
          (if right.val.testBit bit then (1 : ZMod 2) else 0) at hcoordinate
      cases hleft : left.val.testBit bit <;>
        cases hright : right.val.testBit bit <;>
        simp_all
    · have hrankBit : rank ≤ bit := Nat.le_of_not_gt hbit
      have hpopulation := population_le_two_pow_canonicalGradedRank
        population activeBound
      have hleft :
          left.val < 2 ^ bit :=
        left.isLt.trans_le <|
          hpopulation.trans <|
            Nat.pow_le_pow_right (by omega) hrankBit
      have hright :
          right.val < 2 ^ bit :=
        right.isLt.trans_le <|
          hpopulation.trans <|
            Nat.pow_le_pow_right (by omega) hrankBit
      rw [Nat.testBit_eq_false_of_lt hleft,
        Nat.testBit_eq_false_of_lt hright]

theorem canonicalGradedLabel_injective (population activeBound : ℕ) :
    Function.Injective
      (canonicalGradedLabel population activeBound) :=
  (canonicalGradedLabel population activeBound).injective

/-- Odd walk length large enough to reduce failure below a requested
reciprocal denominator. -/
def canonicalWalkLength (denominator : ℕ) : ℕ :=
  2 * Nat.clog 2 (denominator + 1) + 1

theorem canonicalWalkLength_odd (denominator : ℕ) :
    Odd (canonicalWalkLength denominator) := by
  refine ⟨Nat.clog 2 (denominator + 1), ?_⟩
  unfold canonicalWalkLength
  omega

/-- The production length is definitionally a successor, so its finite-row
index is computable without `Fintype.equivFin`. -/
def canonicalWalkSampleFinEquiv (m denominator : ℕ) [NeZero m] :
    MargulisWalkSample m (canonicalWalkLength denominator) ≃
      Fin
        (Fintype.card
          (MargulisWalkSample m (canonicalWalkLength denominator))) := by
  change
    MargulisWalkSample m
        (2 * Nat.clog 2 (denominator + 1) + 1) ≃
      Fin
        (Fintype.card
          (MargulisWalkSample m
            (2 * Nat.clog 2 (denominator + 1) + 1)))
  exact positiveWalkSampleFinEquiv m
    (2 * Nat.clog 2 (denominator + 1))

theorem denominator_succ_le_walk_failure_power (denominator : ℕ) :
    denominator + 1 ≤
      2 ^ (2 * canonicalWalkLength denominator + 4) := by
  calc
    denominator + 1 ≤ 2 ^ Nat.clog 2 (denominator + 1) :=
      Nat.le_pow_clog (by omega) _
    _ ≤ 2 ^ (2 * canonicalWalkLength denominator + 4) :=
      Nat.pow_le_pow_right (by omega) (by
        unfold canonicalWalkLength
        omega)

theorem canonicalWalkFailure_le (denominator : ℕ) :
    1 / (2 : ℝ) ^ (2 * canonicalWalkLength denominator + 4) ≤
      1 / (denominator + 1 : ℕ) := by
  have hdenominatorPositive :
      (0 : ℝ) < (denominator + 1 : ℕ) := by positivity
  have hcast :
      (denominator + 1 : ℕ) ≤
        ((2 : ℝ) ^ (2 * canonicalWalkLength denominator + 4)) := by
    exact_mod_cast denominator_succ_le_walk_failure_power denominator
  exact one_div_le_one_div_of_le hdenominatorPositive hcast

/-- No numeric premises remain: depth, rank, label, terminal sparsity, walk
parity, and the requested reciprocal failure are fixed canonically. -/
noncomputable def tunedCanonicalGradedToeplitzPoweredWalkListCertificate
    (spectrum : ExpanderSpectrumContract)
    (population activeBound denominator : ℕ) :
    AmplifiedListCertificate
      (BoundedActiveSet population activeBound)
      (MargulisWalkSample
        (2 ^ toeplitzWalkSideBits
          (canonicalGradedRank population activeBound))
        (canonicalWalkLength denominator)) :=
  gradedToeplitzPoweredWalkListCertificate spectrum
    (canonicalWalkLength_odd denominator)
    (canonicalGradedDepth_le_rank population activeBound)
    (canonicalGraded_terminal activeBound)
    (canonicalGradedLabel population activeBound)
    (canonicalGradedLabel_injective population activeBound)

theorem tunedCanonicalGradedToeplitzPoweredWalkListCertificate_failure_le
    (spectrum : ExpanderSpectrumContract)
    (population activeBound denominator : ℕ) :
    (tunedCanonicalGradedToeplitzPoweredWalkListCertificate
      spectrum population activeBound denominator).failure ≤
        1 / (denominator + 1 : ℕ) :=
  canonicalWalkFailure_le denominator

end NearCubicWires.SupplierWalkBridge
