import Statement
import Statement_Wire_3_5

/-! # The statement that comparator checks

Row B of Theorem 1.1 (`thm:tradeoff`) of the paper (`paper/paper.tex`), stated from `Statement.lean`,
`Statement_Wire_3_5.lean` and Mathlib alone: the nine published statements of the Theorem 2.5 repository (each defined
in `Statement.lean`, with the sentence it transcribes) imply `rowB` (`Statement_Wire_3_5.lean`: `c = 1/8`,
`K_T = 11/2`, `K_S = 9/2`).

The proof is left open on purpose. `comparator` checks that `Solution.lean` proves exactly this statement. `Check.lean`
does not import this file, and `make` does not build it. -/

set_option warningAsError false

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
  sorry
