import W3.Aliases
import W3.Proof.Foundations.SourceRegistry
import Outer.Apply
import Succinct.Main
import Proof.Foundations.RecoveryScheduleEnvelope

/-! # The short PCP applied once per clock

Replaces the old `fixedProjection`/`outer` (the printed CLW20 Lemma 3.10 entered here and only here). The near-cubic-wires paper,:
order of constants items 3–5 ("The general-oracle exponent G … Then the description exponent G′ … The succinct
hierarchy verifier 𝒱_G … Apply Fact C.1 to them once … The padding constant A_pad …, which fixes the width q(N)").
* `degreeOf` = G = 17·stvExponent (D5: the proof already picks exactly this degree, FinalParametersZeta.lean:41–45);
* `lenRootOf` = 2e + 2 for `oracleSizeBound G ≤ c(n+1)^e`, so λ_ν = ν^{lenRoot+2} (gates Transfer/LenFit);
* `sv` = 𝒱_G of Lemma D.3 for the hierarchy at clock n^{k+2} (gates `Succinct.succinctVerifier_exists`);
* `width` = q(N) (`Outer.width`, Lemma C.5), `apadOf` = A_pad.
`width sources k clock N` replaces every `(outer sources k clock).result.pcp.nativeWidth N`. -/

set_option autoImplicit false

namespace W3

namespace NearCubicWires.RepairSource.SelectedRecoveryIntegration
noncomputable section

end
end NearCubicWires.RepairSource.SelectedRecoveryIntegration

end W3
