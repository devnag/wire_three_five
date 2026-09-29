import Proof.Wire_3_5.Primitive.Writers.Plan

/-! # PA.g7: the THR endpoint exponent (census G7'), the residual `EndpointLeaf`

Realizes the choice of the filters' endpoint error in `lem:primitive`: "For each name, use the regular filter of
filt:gap on its signed mixed-residual population, with cap `B` and an endpoint error chosen as a sufficiently small fixed
inverse power of `n`" (P3:3073-3076), for THR through "the expectation of the reported-list observable differs from
(prim:truth) by an arbitrarily small fixed inverse power of `n`, after choosing the prime and filter errors [...] For
THR this is filt:observable applied to all the polynomially many rows" (P3:3146-3151): the rows are the child
selections `𝒢` of the exact decomposition, polynomially many by the description envelope, so a fixed inverse power of
`n` beats `|𝒢|` times the endpoint error. The exponent is fixed after the decomposition algorithm and before the
envelope ("numerical errors, and every description-size envelope are fixed first", P3:3185-3187).

Paper quantity of the main type: `ThrEndpoint`, `|𝒢|·ξ ≤ n^{−D}/8` with `ξ = 2^{−errExp}` (the hypothesis `hG` of
`thr_call_error` / `greedyValue_error`).

Main results: `endpointExp` (`fe = 112·deg + 4·coef + 7` of the gate's decomposition algorithm), `count_le_pow`
(`8n·(c·((n+1)^26+2)^d+1)^4 ≤ (n+2)^{112d+4c+7}`), `endpoint` (G7' at every call for every free constants with
`filterErrDeg = fe`), and **`endpointLeaf : EndpointLeaf l`**. The child count is Theorem 2.5's
`CloseoutRawRows.selection_count` (`|𝒢| ≤ (a.coefficient·(desc+2)^{a.degree} + 1)^4`) at the call's description bound
`desc = (n+1)^26`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Endpoint
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars

variable (l : Literals)

/-- The gate's exact decomposition algorithm (the `cw19` literal's); it does not depend on the free
constants. -/
noncomputable def gateAlg : RepairRepresentation.DecompositionAlgorithm :=
  Classical.choice l.eightSources.decomposition

/-- **The THR endpoint exponent** `fe = 112·deg + 4·coef + 7` of the gate's decomposition algorithm. -/
noncomputable def endpointExp : ℕ := 112 * (gateAlg l).degree + 4 * (gateAlg l).coefficient + 7

theorem endpointExp_ge : 1 + 2 ≤ endpointExp l := by unfold endpointExp; omega

/-- `8n ≤ (n+2)^3`. -/
theorem eight_mul_le (n : ℕ) : 8 * n ≤ (n + 2) ^ 3 := by
  have h4 : 4 * n ≤ (n + 2) ^ 2 := by nlinarith
  calc 8 * n = 4 * n * 2 := by ring
    _ ≤ (n + 2) ^ 2 * (n + 2) := Nat.mul_le_mul h4 (by omega)
    _ = (n + 2) ^ 3 := by ring

/-- **The arithmetic of G7'**: `8n·(c·((n+1)^{26}+2)^d + 1)^4 ≤ (n+2)^{112d+4c+7}`. -/
theorem count_le_pow (n c d : ℕ) :
    8 * n * (c * ((n + 1) ^ 26 + 2) ^ d + 1) ^ 4 ≤ (n + 2) ^ (112 * d + 4 * c + 7) := by
  have h2 : 2 ≤ n + 2 := by omega
  have hA : (n + 1) ^ 26 + 2 ≤ (n + 2) ^ 28 := by
    have e1 : (n + 1) ^ 26 ≤ (n + 2) ^ 26 := Nat.pow_le_pow_left (by omega) _
    have e2 : 4 ≤ (n + 2) ^ 2 := by nlinarith
    have e3 : 1 ≤ (n + 2) ^ 26 := Nat.one_le_pow _ _ (by omega)
    calc (n + 1) ^ 26 + 2 ≤ (n + 2) ^ 26 * 4 := by omega
      _ ≤ (n + 2) ^ 26 * (n + 2) ^ 2 := Nat.mul_le_mul_left _ e2
      _ = (n + 2) ^ 28 := by rw [← pow_add]
  have hB : ((n + 1) ^ 26 + 2) ^ d ≤ (n + 2) ^ (28 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hA d
  have hX : 1 ≤ (n + 2) ^ (28 * d) := Nat.one_le_pow _ _ (by omega)
  have hc : c + 1 ≤ (n + 2) ^ c := le_trans Nat.lt_two_pow_self (Nat.pow_le_pow_left h2 c)
  have hC : c * ((n + 1) ^ 26 + 2) ^ d + 1 ≤ (n + 2) ^ (c + 28 * d) := by
    calc c * ((n + 1) ^ 26 + 2) ^ d + 1 ≤ c * (n + 2) ^ (28 * d) + (n + 2) ^ (28 * d) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hB) hX
      _ = (c + 1) * (n + 2) ^ (28 * d) := by ring
      _ ≤ (n + 2) ^ c * (n + 2) ^ (28 * d) := Nat.mul_le_mul_right _ hc
      _ = (n + 2) ^ (c + 28 * d) := by rw [← pow_add]
  have hD : (c * ((n + 1) ^ 26 + 2) ^ d + 1) ^ 4 ≤ (n + 2) ^ (4 * c + 112 * d) := by
    calc (c * ((n + 1) ^ 26 + 2) ^ d + 1) ^ 4 ≤ ((n + 2) ^ (c + 28 * d)) ^ 4 := Nat.pow_le_pow_left hC 4
      _ = (n + 2) ^ (4 * c + 112 * d) := by rw [← pow_mul]; congr 1; ring
  calc 8 * n * (c * ((n + 1) ^ 26 + 2) ^ d + 1) ^ 4 ≤ (n + 2) ^ 3 * (n + 2) ^ (4 * c + 112 * d) :=
        Nat.mul_le_mul (eight_mul_le n) hD
    _ = (n + 2) ^ (4 * c + 112 * d + 3) := by rw [← pow_add]; congr 1; ring
    _ ≤ (n + 2) ^ (112 * d + 4 * c + 7) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **G7' at every call**: for every free constants whose endpoint exponent is `fe`, every clock, coefficient and
source work, `|𝒢|·2^{−errExp} ≤ n^{−D}/8` at every THR call. -/
theorem endpoint (F : GateFree l) (hF : F.filterErrDeg = endpointExp l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    ThrEndpoint (callInputs l F kclk coef A a ha) (gate0 l F).alg := by
  intro n a' ha' Cs carriers translation hcall hs
  have hn : 0 < n := by
    have h1 : 2 ≤ ((gate0 l F).budget kclk coef A a ha).rOf n := hs.2.1
    have h2 : 4 * ((gate0 l F).budget kclk coef A a ha).rOf n ≤ n := hs.2.2.1
    omega
  have hdesc : ∀ c ∈ (thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs).circuits,
      c.descriptionBits ≤ (n + 1) ^ 26 := by
    intro c hc
    rw [List.mem_ofFn] at hc
    obtain ⟨i, rfl⟩ := hc
    exact hcall.2.2.1 i
  have hfour : (thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs).circuits.length ≤ 4 := by
    simp only [List.length_ofFn]
    exact ha'
  have hcard := RepairSource.CloseoutRawRows.selection_count (gate0 l F).alg
    (thrRequest ((callInputs l F kclk coef A a ha).starParams n hs) Cs) ((n + 1) ^ 26) hfour hdesc
  have hnat : 8 * n * Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) ≤
      2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) := by
    have hb := count_le_pow n (gateAlg l).coefficient (gateAlg l).degree
    have hpow : (n + 2) ^ endpointExp l ≤ 2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) := by
      rw [hF, mul_comm, pow_mul]
      exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) _
    calc 8 * n * Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
        ≤ 8 * n * ((gateAlg l).coefficient * ((n + 1) ^ 26 + 2) ^ (gateAlg l).degree + 1) ^ 4 :=
          Nat.mul_le_mul_left _ hcard
      _ ≤ (n + 2) ^ endpointExp l := hb
      _ ≤ 2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) := hpow
  show (Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) : ℝ) *
      (1 / 2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2))) ≤ (n : ℝ) ^ (-((1 : ℕ) : ℝ)) / 8
  rw [Nat.cast_one, Real.rpow_neg_one]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : (8 * n : ℝ) * (Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (gate0 l F).alg) : ℝ) ≤ 2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) := by exact_mod_cast hnat
  have h2 : (0 : ℝ) < 2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) := by positivity
  have key : (Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) : ℝ) /
      2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) ≤ 1 / (8 * n) := by
    rw [div_le_div_iff₀ h2 (by positivity)]
    linarith [hR]
  calc (Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) : ℝ) *
        (1 / 2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)))
      = (Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) : ℝ) /
        2 ^ (F.filterErrDeg * Nat.clog 2 (n + 2)) := by ring
    _ ≤ 1 / (8 * n) := key
    _ = (n : ℝ)⁻¹ / 8 := by ring

/-- **The residual `EndpointLeaf`** (PA.g7): the endpoint exponent `fe = 112·deg + 4·coef + 7` with G7' at every call. -/
noncomputable def endpointLeaf : EndpointLeaf l :=
  ⟨endpointExp l, endpointExp_ge l, fun F hF kclk coef A a ha => endpoint l F hF kclk coef A a ha⟩

end NearCubicWires.WireExponent3_5.PrimAsm.Endpoint
