import Statement_Wire_3_5
import Bindings.CTW26_Lemma3_2
import Bindings.CW19_Proposition18_2_TM2
import Bindings.Williams14_Corollary4_4
import Bindings.HLW06_Theorem8_2
import Bindings.RS62_Theorem4
import Bindings.CLW20_Lemma3_10_TM2
import Bindings.CLW20_Lemma3_10_Wrapper
import Bindings.CLW20_Lemma3_11_TM2
import Bindings.CLW20_Theorem1_13
import Bindings.CLW20_Lemma3_8
import Bindings.CLW20_Lemma3_9_TM2

/-! # The literals supply the Theorem 2.5 source bundle

Realizes the use of the imported results in the transfer (P3:3250-3346: the projection PCP, the pointwise PCPP, the
refuter, worst-case amplification and the XOR lemma) through the Theorem 2.5 bundle `EightSources`, which every
recovery donor takes (canonical recovery, the `E^NP` certificate, Cases 1 and 2; P3:3704-3772). The paper quantity
of the main type is that bundle, obtained from the nine literal hypotheses `Literals` by the adapter tuple of
`MainTheorem.lean:57-72`, with the XOR source proved in Lean (`CLW20Lemma38.clw20_xor_source`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5
open NearCubicWires NearCubicWires.RepairSource

/-- The nine literals give `EightSources`, by the Theorem 2.5 adapters. -/
theorem Literals.eightSources (lit : Literals) : EightSources :=
  ⟨Bindings.CTW26.ctw26_to_import lit.ctw26, Bindings.CW19TM2.cw19_tm2_to_import lit.cw19,
    Bindings.Williams14.williams14_to_import lit.williams, Bindings.HLW06.hlw06_to_import lit.hlw06,
    Bindings.RS62.rs62_to_import lit.rs62,
    ⟨Bindings.CLW20Lemma310Guard.clw20_lemma3_10_to_import
        (Bindings.CLW20Lemma310TM2.tier1_of_tier2 lit.clw310),
      Bindings.CLW20Lemma311TM2.clw20_lemma3_11_explicitEnc_tm2_to_import lit.clw311⟩,
    ⟨Bindings.CLW20Theorem113.clw20_theorem1_13_to_import lit.clw113, Bindings.CLW20Lemma38.clw20_xor_source⟩,
    Bindings.CLW20Lemma39TM2.clw20_lemma3_9_tm2_to_import lit.clw39⟩

end NearCubicWires.WireExponent3_5
