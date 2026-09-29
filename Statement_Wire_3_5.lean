import Statement

/-! # The headline theorem `WireExponent3_5` (paper3 `thm:tradeoff`) at row B

Realizes `thm:tradeoff` (P3:225-238) and its row B (P3:261-262): "There is a language `F ∈ E^NP` such that,
for every pair of fixed constants `A_T, A_S > 0`, there is `n_0` for which, for every `n ≥ n_0`,
`W(C) ≤ A_T n^{7/2}/L(n)^{K_T}, C ∈ THR∘THR ⟹ agr(F_n, C) < 1/2 + L(n)^{-c}`" and the same for `SYM∘THR` with
`A_S`, `K_S`. Row B is `c = 1/8`, `K_T = 11/2`, `K_S = 9/2`, the paper's named formalization target
(P3:1082-1085).

Main types: `WireExponent3_5 c K_T K_S` and `rowB`. The quantities they name are the wire count `W(C)` (P3:213-216:
bottom support plus one; the THR tops of weight zero are dropped, which gives the same theorem by `rowB_iff_raw` in
`StatementChecks/Wire_3_5_Readings.lean`), the agreement `agr(F_n, C)` (P3:217-218), `L(n) = ⌈log₂(n+2)⌉` (P3:208)
and `E^NP` (P3:220-223), all in the vocabulary of the Theorem 2.5 `Statement`.

`Literals` bundles the nine literal hypotheses of the Theorem 2.5 repository
(`github.com/devnag/near-cubic-wires`, its `Check.lean`), one field per literal Prop of `Statement`, in the same
order. The target is `Literals → rowB`. The matrix concentration bound cited at
P3:2812-2813 is not a hypothesis: the sampler moment is proved directly. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5
open NearCubicWires NearCubicWires.RepairSource

/-- The hardness half of `thm:tradeoff` for one language (P3:233-237): for every pair of fixed multipliers there
is an onset past which every capped circuit of either class has agreement below `1/2 + L(n)^{-c}`. -/
noncomputable def WireExponent3_5Hard (c KT KS : ℝ) (language : Language) : Prop :=
  ∀ AT AS : ℝ, 0 < AT → 0 < AS →
    ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
      (∀ circuit : ThresholdThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            if circuit.topWeight i = 0 then 0
            else (circuit.bottom i).support.card + 1 : ℕ) : ℝ) ≤
          AT * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KT →
        ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) <
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)) ∧
      (∀ circuit : SymmetricThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            ((circuit.bottom i).support.card + 1) : ℕ) : ℝ) ≤
          AS * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KS →
        ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) <
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c))

/-- `thm:tradeoff` (P3:225-238): one `E^NP` language, chosen before the multipliers `A_T, A_S`. -/
noncomputable def _root_.NearCubicWires.WireExponent3_5 (c KT KS : ℝ) : Prop :=
  ∃ language : Language,
    (∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
        Nonempty (OrdinaryENPCertificate oracle language)) ∧
    WireExponent3_5Hard c KT KS language

/-- Row B (P3:261-262): `c = 1/8`, `K_T = 11/2`, `K_S = 9/2`. -/
noncomputable def rowB : Prop := WireExponent3_5 (1 / 8) (11 / 2) (9 / 2)

/-- The nine literal hypotheses of the Theorem 2.5 repository (`github.com/devnag/near-cubic-wires`, its
`Check.lean` and `MainTheorem.lean`), in order. Each field is one literal Prop of `Statement`, transcribing a
printed statement of the cited paper. -/
structure Literals : Prop where
  ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2
  cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2
  williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4
  hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2
  rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314
  clw310 : NearCubicWires.Bindings.CLW20Lemma310TM2.CLW20_Lemma3_10_TM2
  clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2
  clw113 : NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13
  clw39 : NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2

end NearCubicWires.WireExponent3_5
