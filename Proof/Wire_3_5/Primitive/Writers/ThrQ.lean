import Proof.Wire_3_5.Primitive.Writers.SymQ

/-! # PA library (b), THR numbers: the THR sample count `Q` as a closed formula

`samp:q` (P3:2987-2988, 3154-3162) at a THR call: `Q = thrCount = sampleCount(kh, D, n, |T|·(2|𝒢|·cutoff + 1)² + 1)`,
where `|T| = |GapSeed|·|𝒢|·Σ_{p ≤ cutoff prime} p` counts the call's state matrices (the final seed, the equation
`g ∈ 𝒢`, the prime `p` and the residue `s mod p`; row:matrix), `|𝒢| = Π_i |children_i|` (the child selections,
row:threshold-rows P3:2543-2551) and the prime cutoff is Theorem 2.5's tuned surrogate's
`(max 24 (6(e+1)(K+1)))²` with `e = ⌈log₂(Σ_g ‖L_g‖ + 1)⌉` and `K = 8(|𝒢|+1)n^D` (P3:2551-2558).

- **`thrCount_eq`**: `SeedFix.thrCount alg I hs Cs = thrQval I.D kh n seedBits |𝒢| cutoff`;
- **`thrCutoff_eq`**: the cutoff from the sum over the selections of the equations' magnitude bounds;
- `card_thrEq`: `|𝒢| = Π_i |children_i|`; `card_primeRows`: `|Σ_{p} ZMod p| = Σ_{p ≤ c prime} p`.

A machine computing `Q` evaluates exactly these: the child counts, the equations' magnitudes over all selections,
the primes up to the cutoff, and `sampleCount`.

Paper quantity of the main type: `SeedFix.thrCount` (`thrCount_eq`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrQ
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime

/-- `Σ_{p ≤ c prime} p`: the number of `(p, s mod p)` rows. -/
def primeSum (c : ℕ) : ℕ := ∑ p ∈ primesUpTo c, p

/-- **The THR sample count as a formula** in the seed bits, `|𝒢|` and the cutoff. -/
def thrQval (D kh n seedBits G c : ℕ) : ℕ :=
  Sampler.sampleCount kh D n (2 ^ seedBits * (G * primeSum c) * (2 * G * c + 1) ^ 2 + 1)

theorem card_primeRows (c : ℕ) : Fintype.card (Σ pr : PrimeIndex c, ZMod pr.val) = primeSum c := by
  rw [Fintype.card_sigma]
  simp only [ZMod.card]
  exact Finset.sum_coe_sort (primesUpTo c) id

theorem card_thrEq (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) :
    Fintype.card (ThrEq P Cs alg) =
      ∏ i : Fin (List.ofFn Cs).length, (RepairOrdinary.ThresholdRows.children alg ((List.ofFn Cs).get i)).length := by
  unfold ThrEq RepairOrdinary.ThresholdRows.Selection
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **`Q` at a THR call**: the sample count is the formula at the call's numbers. -/
theorem thrCount_eq (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) :
    SeedFix.thrCount alg I hs Cs =
      thrQval I.D (SeedFix.callKh (I.starParams n hs)) n (I.filterParams .thr n).seedBits
        (Fintype.card (ThrEq (I.starParams n hs) Cs alg))
        (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) := by
  unfold SeedFix.thrCount thrQval SeedFix.thrMassNat
  refine congrArg (Sampler.sampleCount _ _ _) ?_
  rw [Fintype.card_prod, Fintype.card_prod, card_gapSeed, card_primeRows]

/-- The THR denominator `K = 8(|𝒢|+1)n^D` (the prime surrogate's error and the lists' target). -/
theorem thrCallDen_eq (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) :
    thrCallDen alg I hs Cs = 8 * (Fintype.card (ThrEq (I.starParams n hs) Cs alg) + 1) * n ^ I.D := rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrQ
