import Close.Amplifier
import Outer.Source
import Outer.Supply
import Bindings.CLW20_Lemma3_10
import Proof.CaseAnalysis.FinalTapeLocality
import Bindings.CLW20_Lemma3_8

/-!
# The gate chain's source bundle (J1)

Proof 1's transfer chain is parametrized by `NearCubicWires.RepairSource.EightSources`, which also contains the
expander bound (HLW06), the prime θ bound (RS62), CW19 Proposition 18(2) and the two-query PCPP (CLW20 Lemma 3.11).
None of those is among the nine inputs of the main theorem, so `EightSources` is NEVER instantiated here. The gate
chain uses `GateSources`, built from `NineInputs` by proof 1's own proved adapters, and re-hosts the few
`EightSources`-level wrappers (`padding`, `outer`, `hierarchy`, ...) over it. The XOR lemma is proved in proof 1
(`CLW20Lemma38.clw20_xor_source`) and costs no input.
-/

set_option autoImplicit false

namespace NearCubicGates.Close

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation

/-- The internal source objects the gate chain consumes, one per published input. -/
structure GateSources : Prop where
  normalization : ThresholdNormalizationContract
  williams : WilliamsSource
  /-- Input 6 (Murray–Williams' short PCP as an oracle circuit), in the ordinary model (the near-cubic-gates paper imp:short-pcp). -/
  mw : NearCubicGates.Close.Outer.MWSource
  /-- lem:succinct-verifier for every clock (the near-cubic-gates paper, app:multitape; proved in `Succinct`). -/
  succinct : NearCubicGates.Close.Outer.SuccinctSupply
  hierarchyRefuter : HierarchyRefuterSource
  xor : XorSource
  amplifier : Nonempty SourceAmplifierFactory
  restriction : NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction
  bernstein : NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}
  primes : NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem
  threeQueryPCPP : NearCubicGates.PublishedSources.PCPP.ThreeQuerySourceGroup
  /-- Input 1 itself (CTW26 Lemma 3.2), for the integer descriptions of guessed circuits (the near-cubic-gates paper's fixed weak machine: "Only existence of normalized integer descriptions is required"). -/
  normalizationLemma : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2

end NearCubicGates.Close
