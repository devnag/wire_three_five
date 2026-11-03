import Proof.Wire_3_5.Assembly.Final
import Proof.Wire_3_5.Assembly.ConeMono

/-! # Row B of Theorem 1.1 from nine published statements, and Theorem 1.1 on the cone above row B

`rowB_from_literature` proves row B of Theorem 1.1 of the paper (`paper/paper.tex`, `thm:tradeoff`, Table 1: `c = 1/8`,
`K_T = 11/2`, `K_S = 9/2`; in Lean `NearCubicWires.WireExponent3_5.rowB`, defined in `Statement_Wire_3_5.lean`) from
nine hypotheses. The first seven are Lean transcriptions of statements printed in the cited papers, defined in
`Statement.lean` with each sentence quoted verbatim and its PDF page; the last two are CLW20 Theorem 1.13 and
Lemma 3.9 at the range the proof uses, defined in `Statement_Wire_3_5.lean` (`StatementChecks/Wire_3_5_Inputs.lean`
proves that the printed statements imply them).
The matrix concentration bound the paper cites for its sampler is not a hypothesis: the sampler moment is proved
directly.

`rowBCone_from_literature` proves, from the same nine hypotheses, Theorem 1.1 for every `0 < c ≤ 1/8`, `K_T ≥ 11/2`,
`K_S ≥ 9/2` (`NearCubicWires.WireExponent3_5.rowBCone`, defined in `Statement_Wire_3_5.lean`): row B, then the
monotonicity of Theorem 1.1 in its parameters (`wireExponent3_5_mono`: a larger allowed advantage and smaller caps). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5

/-- Row B of Theorem 1.1 (`paper/paper.tex`, `thm:tradeoff`) from nine literal paper statements. -/
theorem rowB_from_literature
    (ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2)
    (cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2)
    (williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2)
    (rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314)
    (mw20 : NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2)
    (clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : NearCubicWires.WireExponent3_5.CLW20_Theorem1_13_Poly)
    (clw39 : NearCubicWires.WireExponent3_5.CLW20_Lemma3_9_TM2_Large) : rowB :=
  Assembly.rowB_closed ⟨ctw26, cw19, williams, hlw06, rs62, mw20, clw311, clw113, clw39⟩

/-- Theorem 1.1 (`paper/paper.tex`, `thm:tradeoff`) for every `0 < c ≤ 1/8`, `K_T ≥ 11/2`, `K_S ≥ 9/2`, from the same
nine literal paper statements. -/
theorem rowBCone_from_literature
    (ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2)
    (cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2)
    (williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2)
    (rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314)
    (mw20 : NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2)
    (clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : NearCubicWires.WireExponent3_5.CLW20_Theorem1_13_Poly)
    (clw39 : NearCubicWires.WireExponent3_5.CLW20_Lemma3_9_TM2_Large) : rowBCone :=
  rowBCone_of_rowB (rowB_from_literature ctw26 cw19 williams hlw06 rs62 mw20 clw311 clw113 clw39)

end NearCubicWires.WireExponent3_5
