import MainTheorem_Wire_3_5

/-! # The proof that comparator checks

The statements of `Challenge.lean`, proved by the main theorems (`MainTheorem_Wire_3_5.lean`). -/

theorem NearCubicWires.wireExponent3_5_rowB_from_literature
    (ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2)
    (cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2)
    (williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2)
    (rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314)
    (mw20 : NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2)
    (clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : NearCubicWires.WireExponent3_5.CLW20_Theorem1_13_Poly)
    (clw39 : NearCubicWires.WireExponent3_5.CLW20_Lemma3_9_TM2_Large) :
    NearCubicWires.WireExponent3_5.rowB :=
  NearCubicWires.WireExponent3_5.rowB_from_literature
    ctw26 cw19 williams hlw06 rs62 mw20 clw311 clw113 clw39

theorem NearCubicWires.wireExponent3_5_rowBCone_from_literature
    (ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2)
    (cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2)
    (williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2)
    (rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314)
    (mw20 : NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2)
    (clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : NearCubicWires.WireExponent3_5.CLW20_Theorem1_13_Poly)
    (clw39 : NearCubicWires.WireExponent3_5.CLW20_Lemma3_9_TM2_Large) :
    NearCubicWires.WireExponent3_5.rowBCone :=
  NearCubicWires.WireExponent3_5.rowBCone_from_literature
    ctw26 cw19 williams hlw06 rs62 mw20 clw311 clw113 clw39
