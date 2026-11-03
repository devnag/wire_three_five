import Proof.Wire_3_5.Foundations.SkeletonBase
import Proof.Wire_3_5.Stars.StarCarrier

/-! # Consumer check: carrier containment and the regular filters at a primitive call

Realizes, at the seed's call hypothesis `PrimitiveInputs.Call` (after the fold of), the two duties that
`lem:primitive` (P3:3071-3086) puts on the carrier data of a call: "whose gates are contained in these carriers" makes
each circuit's signed mixed-residual population at most the named populations `Σ_X R_X`, at every star point and at
every input through its decomposition in the call's translation; and "the regular filter of filt:gap on its signed
mixed-residual population" (P3:3074-3076) reads a vector `Z` within the filter's length bound `M`
(`filt:gap`, P3:2019-2025), so the filter's guarantee applies.

Main results: `call_population_le`, `call_inputPopulation_le`, `length_residualBits`, `call_residualBits_len`, and
`mask_of_call` (at a call the mask is the product of the named carriers' `filt:gap` filters). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- The residual vector has two bits per atom occurrence. -/
theorem length_residualBits {n : ℕ} (X : Carrier n) (c u v : BitInput n) :
    (Carrier.residualBits X c u v).length = 2 * X.length := by
  induction X with
  | nil => rfl
  | cons g X ih =>
    simp only [Carrier.residualBits, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    rw [ih]; ring

/-- At a call, the mask is the product of the named carriers' `filt:gap` regular filters at the call's translation,
with the common seed (P3:3078-3080). -/
theorem mask_of_call (I : PrimitiveInputs B) {req : PrimRequest} (hs : I.StarAt req.n) (e : I.Seed req.mode req.n)
    (x : BitInput req.n) :
    I.mask req e x = req.carriers.all fun X => gapFilter (I.filterParams req.mode req.n) e
      (inputResidualBits (I.starParams req.n hs) ((I.starParams req.n hs).translationOfCodes req.translation) X x) := by
  unfold PrimitiveInputs.mask
  rw [dif_pos hs]

end NearCubicWires.WireExponent3_5.Stars
