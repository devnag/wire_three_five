import Proof.Wire_3_5.Assembly.Final

/-! # Row B of Theorem 1.1 from nine published statements

`rowB_from_literature` proves row B of Theorem 1.1 of the paper (`paper/paper.tex`, `thm:tradeoff`, Table 1: `c = 1/8`,
`K_T = 11/2`, `K_S = 9/2`; in Lean `NearCubicWires.WireExponent3_5.rowB`, defined in `Statement_Wire_3_5.lean`) from
nine hypotheses. They are the nine hypotheses of the Theorem 2.5 repository: each is a Lean transcription of a
statement printed in the cited paper, defined in `Statement.lean` with its sentence quoted verbatim and its PDF page.
The matrix concentration bound the paper cites for its sampler is not a hypothesis: the sampler moment is proved
directly. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5

/-- Row B of Theorem 1.1 (`paper/paper.tex`, `thm:tradeoff`) from nine literal paper statements. -/
theorem rowB_from_literature
    (ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2)
    (cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2)
    (williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2)
    (rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314)
    (clw310 : NearCubicWires.Bindings.CLW20Lemma310TM2.CLW20_Lemma3_10_TM2)
    (clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13)
    (clw39 : NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2) : rowB :=
  Assembly.rowB_closed ⟨ctw26, cw19, williams, hlw06, rs62, clw310, clw311, clw113, clw39⟩

end NearCubicWires.WireExponent3_5

