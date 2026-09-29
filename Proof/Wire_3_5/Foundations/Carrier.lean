import Proof.Wire_3_5.Foundations.StarPartition
import Proof.Foundations.SupplierPipeline

/-! # Named carriers, their signed mixed-residual populations, and carrier containment: definitions

Realizes the carrier data of `lem:primitive` (P3:3071-3086): "Fix a polynomial global family of named carriers
[...] For each name, use the regular filter of filt:gap on its signed mixed-residual population [...] For a fixed
tuple of circuits `C_1,…,C_a` in either class mode, whose gates are contained in these carriers", with "Constants,
complemented atoms, and the systematic encoding parity are permitted at the same fixed description envelope"
(P3:3092-3094). A carrier is the union of a named variable's atoms' bottom gates, plus the systematic encoding parity
(`tr:masks`, P3:3401-3410), and "`R_X` counts mixed residuals in the union for `X`" (P3:3419); `star:selection`
(P3:1331) writes `R_X = Σ_{i∈X}(Z_i^+ + Z_i^-)`, and `filt:gap` (P3:2019) reads the population as a bit vector `Z`
of weight `w(Z) = R_X`. The carriers of one run are guessed data (P3:3669-3674), so a primitive call carries its
named carriers.

Main definitions (namespace `NearCubicWires.WireExponent3_5.Stars`):
* `Carrier n`: a named carrier, a finite multiset (a list: repeated labelled occurrences are kept, P3:1361-1362) of
  bottom integer threshold atoms;
* `Carrier.population X c u v`: `R_X = Σ_{i∈X}(Z_i^+ + Z_i^-)` at the star point `(c, u, v)`, with the indicators
  `Z^±` of S0 (P3:1231-1233); `Carrier.residualBits`: its bit vector `Z`;
* `inputResidualBits P σ X x`, `inputPopulation P σ X x`: the same at an input `x`, through its decomposition
  `x = c + u + v` in the partition `σ` (`star:partition`), the vector the call's regular filter reads;
* `thrGates`, `symGates`: the gates of a circuit, as its wire count charges them;
* `GatesIn`: "whose gates are contained in these carriers" — each circuit's gate list is a sub-multiset of the union
  of the named carriers;
* `Carrier.WithinEnvelope`: the carriers' fixed description envelope; `Carrier.code`: the canonical code.

Their proofs (the population bounds, containment's duty `GatesIn.population_le`, the wire bounds) are the component
modules `Proof.Wire_3_5.Stars.StarCarrier` and `Proof.Wire_3_5.Stars.StarCarrierPopulation`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.CanonicalBinary

/-- A named carrier at length `n` (P3:3071-3072, 3401-3410): a finite multiset of bottom integer threshold atoms. -/
abbrev Carrier (n : ℕ) := List (NormalizedThresholdGate n)

namespace Carrier
variable {n : ℕ}

/-- One atom's contribution `Z⁺ + Z⁻` to the population at the star point `(c, u, v)` (P3:1231-1233, 1331). -/
def atomResidual (g : NormalizedThresholdGate n) (c u v : BitInput n) : ℕ :=
  (residualPlus g.eval c u v).toNat + (residualMinus g.eval c u v).toNat

/-- **The signed mixed-residual population** `R_X(c,u,v) = Σ_{i∈X}(Z_i^+ + Z_i^-)` (P3:1331, 3419), counted with
the carrier's multiplicities. -/
def population (X : Carrier n) (c u v : BitInput n) : ℕ :=
  (X.map fun g => atomResidual g c u v).sum

/-- The population as the bit vector `Z` of `filt:gap` (P3:2019): `Z⁺_i, Z⁻_i` for every atom occurrence. -/
def residualBits (X : Carrier n) (c u v : BitInput n) : List Bool :=
  X.flatMap fun g => [residualPlus g.eval c u v, residualMinus g.eval c u v]

/-- The fixed description envelope of a named carrier (P3:3071-3072, 3092-3094): at most `(n+1)^deg` atom
occurrences, each with at most `(n+1)^deg` description bits. -/
def WithinEnvelope (deg : ℕ) (X : Carrier n) : Prop :=
  X.length ≤ (n + 1) ^ deg ∧ ∀ g ∈ X, g.encodingBits ≤ (n + 1) ^ deg

/-- The canonical code of a carrier (the Theorem 2.5 list codecs): a balanced list of atom codes. -/
def code (X : Carrier n) : ℕ :=
  encodeBalancedList (X.map fun g => encodeTaggedList [encodeIntList (List.ofFn g.weight), encodeInt g.threshold])

end Carrier

/-- The residual bit vector `Z` of a carrier at the input `x`, through its decomposition `x = c + u + v` in the
partition `σ` (P3:1220-1222, 3419): the vector the carrier's regular filter reads (P3:3074-3076, 3432-3436). -/
def inputResidualBits (P : StarParams) (σ : P.Translation) (X : Carrier P.n) (x : BitInput P.n) : List Bool :=
  Carrier.residualBits X (P.center σ x) (P.errorVector P.leftBlock (P.leftErrors σ x))
    (P.errorVector P.rightBlock (P.rightErrors σ x))

/-- `R_X(x)`: the population of a carrier at the input `x` in the partition `σ` (P3:3415-3419). -/
def inputPopulation (P : StarParams) (σ : P.Translation) (X : Carrier P.n) (x : BitInput P.n) : ℕ :=
  Carrier.population X (P.center σ x) (P.errorVector P.leftBlock (P.leftErrors σ x))
    (P.errorVector P.rightBlock (P.rightErrors σ x))

/-- The charged gates of a `THR∘THR` circuit: the bottoms at retained top positions (the only bottoms its function
and its wire count see). -/
def thrGates {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) : Carrier n :=
  ((List.finRange C.bottomCount).filter fun i => decide (i ∈ C.top.support)).map fun i => (C.bottom i).gate

/-- The charged gates of a `SYM∘THR` circuit: every bottom. -/
def symGates {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) : Carrier n :=
  (List.finRange C.bottomCount).map fun i => (C.bottom i).gate

/-- **"Whose gates are contained in these carriers"** (P3:3083-3086): the charged gates of each circuit of the
tuple form a sub-multiset of the union of the call's named carriers. Repeated occurrences must be carried with
their multiplicity, so the residual population of every circuit is charged to the named populations. -/
def GatesIn {n a : ℕ} (gates : Fin a → Carrier n) (named : List (Carrier n)) : Prop :=
  ∀ i, (gates i).Subperm named.flatten

end NearCubicWires.WireExponent3_5.Stars
