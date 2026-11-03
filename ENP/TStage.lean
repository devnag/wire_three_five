import ENP.TEmitProg
import ENP.T8Dock
import ENP.T8Meaning
import ENP.T8CostPoly
import ENP.TBytes
import ENP.T8PECost

/-!
# Stage 2: `ENP.TStageRuns` (the glue)

The near-cubic-gates paper's uniform recovery (sec:all-lengths, E^NP paragraph): "Second, the algorithm of imp:short-pcp is run deterministically on
`⟨B*_src⟩_ν` …; a formula with one variable per oracle address and the constraints `C^O_{⟨B*_src⟩_ν}(R) = 0` for all
`2^{ℓ_out}` inputs `R`, of size `2^{2ℓ_out}q^{O_{G,C_clk}(1)} = 2^{O(q)}` (each oracle gate becomes a selector over the
`2^{ℓ_out}` oracle variables), finds the first oracle `O*`."

The pieces:
* the stage-2 emitter `TEmit.tProgOf_of` (prologue, seeds loop `TEmit.seedsRuns_of`, epilogue), with the byte bound
  `tBytesSpec` and the cost bounds `T8.seedsCostPoly` and `T8.pECostPoly`;
* the docking with proof 1's serializer and SAT prefix search `T8.tStageOf`;
* the meaning of flag and prefix `T8.tFlagSpec`, `T8.tTableSpec`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

/-- **Stage 2 of the E^NP recovery**, given the prologue/epilogue cost bound (piece P7). -/
theorem tStageRuns_of (hPE : TEmit.PECostPoly) : TStageRuns :=
  T8.tStageOf (TEmit.tProgOf_of (TEmit.seedsRuns_of tBytesSpec T8.seedsCostPoly) tBytesSpec hPE)
    T8.tFlagSpec T8.tTableSpec

/-- **Stage 2 of the E^NP recovery** (the near-cubic-gates paper's uniform recovery): the first honest oracle table of the oracle circuit `C`
(`TStage`: flag `∃ honest table`, the first one framed), by SAT prefix self-reduction on the stage-2 circuit `c_T`. -/
theorem tStageRuns : TStageRuns := tStageRuns_of T8.pECostPoly

end NearCubicGates.Close.ENP
