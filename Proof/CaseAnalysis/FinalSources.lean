import Proof.Foundations.SourceRegistry
import Proof.CaseAnalysis.RawRowsThresholdAccuracy

/-! The four `EightSources` fields that no closeout consumer binds yet.

`pcp.projection`, `pcp.proximity`, `refuterXor.hierarchyRefuter`, `refuterXor.xor`,
`amplifier` and `normalization` already reach the closeout corpus. `williams`,
`decomposition`, `expander` and `prime` do not: the 244 theorems taking a
`WilliamsAlgorithm` and the 119 taking a `DecompositionAlgorithm` leave them as
free parameters, and the two spectral/Chebyshev contracts are consumed only
inside the imported mathematics.

This module chooses each of the four ONCE, so that every downstream machine,
budget and accuracy theorem is instantiated at the same values and the literal
endpoint genuinely depends on all eight sources. It adds no premise: each
binding is a projection of `EightSources` plus, for the two `Nonempty` sources,
`Classical.choice` -- exactly the pattern `EightSources.hierarchy`,
`EightSources.amplification` and `CloseoutLanguage.selectedPCPP` already use. -/
namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairRepresentation SourceInterfaces SupplierPipeline RepairOrdinary ExecutableInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The selected exact rectangular-product algorithm (paper Appendix B). Every
estimator machine is built over this one value. -/
def williamsOf (sources : EightSources) : WilliamsAlgorithm :=
  Classical.choice sources.williams

/-- The selected disjoint exact-decomposition algorithm (paper A.12). -/
def decompositionOf (sources : EightSources) : DecompositionAlgorithm :=
  Classical.choice sources.decomposition

/-- Gabber-Galil spectral radius, used by the threshold powered walk (paper A.5,
A.9 item 4). -/
theorem expanderOf (sources : EightSources) : ExpanderSpectrumContract :=
  sources.expander

/-- Rosser-Schoenfeld Chebyshev theta, used by the prime surrogate (paper A.6,
A.9 item 5). -/
theorem primeOf (sources : EightSources) : PrimeThetaBoundContract :=
  sources.prime

end
end NearCubicWires.RepairSource.CloseoutFinal
