import MainTheorem_Wire_3_5

/-! # The proof that comparator checks

The statement of `Challenge.lean`, proved by the main theorem (`MainTheorem_Wire_3_5.lean`). -/

theorem NearCubicWires.wireExponent3_5_rowB_from_literature
    (ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2)
    (cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2)
    (williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2)
    (rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314)
    (clw310 : NearCubicWires.Bindings.CLW20Lemma310TM2.CLW20_Lemma3_10_TM2)
    (clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13)
    (clw39 : NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2) :
    NearCubicWires.WireExponent3_5.rowB :=
  NearCubicWires.WireExponent3_5.rowB_from_literature
    ctw26 cw19 williams hlw06 rs62 clw310 clw311 clw113 clw39
