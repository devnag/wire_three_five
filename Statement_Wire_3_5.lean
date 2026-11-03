import Statement

/-! # The headline theorem `WireExponent3_5` (paper3 `thm:tradeoff`) at row B

Realizes `thm:tradeoff` (P3:225-238) and its row B (P3:261-262): "There is a language `F ∈ E^NP` such that,
for every pair of fixed constants `A_T, A_S > 0`, there is `n_0` for which, for every `n ≥ n_0`,
`W(C) ≤ A_T n^{7/2}/L(n)^{K_T}, C ∈ THR∘THR ⟹ agr(F_n, C) < 1/2 + L(n)^{-c}`" and the same for `SYM∘THR` with
`A_S`, `K_S`. Row B is `c = 1/8`, `K_T = 11/2`, `K_S = 9/2`, the paper's named formalization target
(P3:1082-1085).

Main types: `WireExponent3_5 c K_T K_S`, `rowB`, and `rowBCone` (`thm:tradeoff` for every `0 < c ≤ 1/8`,
`K_T ≥ 11/2`, `K_S ≥ 9/2`). The quantities they name are the wire count `W(C)` (P3:213-216: bottom support plus one;
the THR tops of weight zero are dropped, which gives the same theorem by `rowB_iff_raw` in
`StatementChecks/Wire_3_5_Readings.lean`), the agreement `agr(F_n, C)` (P3:217-218), `L(n) = ⌈log₂(n+2)⌉` (P3:208)
and `E^NP` (P3:220-223), all in the vocabulary of the Theorem 2.5 `Statement`.

`Literals` bundles the nine hypotheses. Fields 1–7 are literal Props of the Theorem 2.5 `Statement`
(`github.com/devnag/near-cubic-wires`), in the order of its `Check.lean`; fields 8 and 9 are its CLW20 Theorem 1.13
and Lemma 3.9 at the range the proof uses (defined below; `StatementChecks/Wire_3_5_Inputs.lean` proves that the
printed statements imply them). The targets are `rowB` and `rowBCone`. The matrix concentration bound cited at
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

/-- `thm:tradeoff` (P3:225-238) for every advantage exponent `0 < c ≤ 1/8` and cap exponents `K_T ≥ 11/2`,
`K_S ≥ 9/2`. Each such triple satisfies the theorem's hypotheses `K_T > 5 + 2c`, `K_S > 4 + 2c`; compared with row B
it allows a larger advantage `L(n)^{-c}` and has smaller caps `A n^{7/2}/L(n)^K`. -/
noncomputable def rowBCone : Prop :=
  ∀ c KT KS : ℝ, 0 < c → c ≤ 1 / 8 → 11 / 2 ≤ KT → 9 / 2 ≤ KS → WireExponent3_5 c KT KS

/-- **Input 8**: CLW20 Theorem 1.13 ("For every time-constructible function T(n) such that n ≤ T(n) ≤ 2^{poly(n)}, there is
a language L ∈ NTIME[T(n)] and an algorithm R such that …", PDF p. 6) at the polynomial clocks `T(n) = n^(k+2)`, each of
which is time-constructible with `n ≤ T(n) ≤ 2^{poly(n)}`: the hierarchy clocks the proof uses. -/
def CLW20_Theorem1_13_Poly : Prop :=
  ∀ k : ℕ, NearCubicWires.Bindings.CLW20Theorem113.Theorem1_13At (fun n => n ^ (k + 2))

/-- **Input 9**: CLW20 Lemma 3.9 ("There is a constant c ≥ 1 such that, for any time-constructible function S(n) and every
f : {0,1}^n → {0,1} that does not have (general) circuits of size S(n). There is a function g : {0,1}^{O(n)} → {0,1} that
cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size S(n)^{1/c}. Furthermore, given the 2^n-length truth table
of f, the truth table of g can be constructed in 2^{O(n)} time.") at the functions `S(n) ≥ n^c`: the regime in which
STV01 state the parameters of its source, Theorem 24 (`ℓ < s^γ`). -/
def CLW20_Lemma3_9_TM2_Large : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, NearCubicWires.SourceInterfaces.TimeConstructible S →
    (∀ n : ℕ, (n : ℝ) ^ c ≤ (S n : ℝ)) →
    Nonempty (NearCubicWires.Bindings.CLW20Lemma39TM2.Lemma3_9AtTM2 c S)

/-- The nine literal hypotheses, in order. Fields 1–7 are literal Props of `Statement`, each transcribing a printed
statement of the cited paper (the sixth is the Murray–Williams short PCP); fields 8 and 9 are the literal Props of
`Statement` for CLW20 Theorem 1.13 and Lemma 3.9 restricted to the range the proof reads (defined above). -/
structure Literals : Prop where
  ctw26 : NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2
  cw19 : NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2
  williams : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4
  hlw06 : NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2
  rs62 : NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314
  mw20 : NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2
  clw311 : NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2
  clw113 : CLW20_Theorem1_13_Poly
  clw39 : CLW20_Lemma3_9_TM2_Large

end NearCubicWires.WireExponent3_5
