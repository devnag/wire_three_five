import Statement
import Statement_Wire_3_5

/-! # The statements that comparator checks

Row B of Theorem 1.1 (`thm:tradeoff`) of the paper (`paper/paper.tex`), stated from `Statement.lean`,
`Statement_Wire_3_5.lean` and Mathlib alone: nine published statements imply `rowB` (`Statement_Wire_3_5.lean`:
`c = 1/8`, `K_T = 11/2`, `K_S = 9/2`). The first seven are defined in `Statement.lean`, with the sentence each
transcribes; the last two are CLW20 Theorem 1.13 and Lemma 3.9 at the range the proof uses, defined in
`Statement_Wire_3_5.lean`. From the same nine statements, the second theorem gives Theorem 1.1 for every
`0 < c ≤ 1/8`, `K_T ≥ 11/2`, `K_S ≥ 9/2` (`rowBCone`, `Statement_Wire_3_5.lean`).

The proofs are left open on purpose. `comparator` checks that `Solution.lean` proves exactly these two statements.
`Check.lean` does not import this file, and `make` does not build it. -/

set_option warningAsError false

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
  sorry

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
  sorry
