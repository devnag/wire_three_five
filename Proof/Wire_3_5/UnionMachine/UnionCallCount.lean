import Proof.Wire_3_5.Assembly.Free

/-! # The union's call-count forcing lemma (P3:3622, 3797-3798)

Realizes, at the pinned setup `S₂` and the pinned oracle degree `G = 17·c_STV`, the count behind "There are polynomially
many calls when `Λ̄ = q^{O(1)}`" (P3:3622) and "the time for all polynomially many verification calls has the form
[...]" (P3:3797-3798): every guess the union machine can process (oracle of size at most `q^G`, the machine's first
check, P3:3669) schedules at most `q(N)^{gateCallDeg l G}` primitive calls, eventually in `N`, where `q(N)` is the
ledger's native width, the `q` of `tr:time`'s split `q(N)^{callDeg}·callBudget(q(N))`.

The count is `length_schedule_le`, `#calls ≤ 24K(1 + 2K(s+1))⁴` with `K = c_a (size(H)+1)^{d_a}` the PCPP's
clause/variable bound on the substituted circuit `H`. Two facts force the exponent `gateCallDeg = 5σ_H d_a + 1`,
`σ_H = max(e_Q + 2^{oracleDepth G}, 3e_Q)`:
* the substituted circuit of an oracle within `q^G` has `size(H) + 1 ≤ K_s (q+1)^{σ_H}` (base's
  `compactSubstituted_size`, `request_size`, the PCP's query bound; `requestSize_le_of`), so `K ≤ K₀ (q+1)^{σ_H d_a}`;
* the grid size `s(q)` obeys `s⁸ ≤ C_sp L³` (`RowBParams.sp_le`), so `C (s+1)⁴ ≤ q` eventually for every constant `C`
  (`eventually_calls`); the `+1` of `gateCallDeg` absorbs it with all constants.

Paper quantity of the main type: **the number of scheduled primitive calls**, `(g.checkData tr).schedule.length`,
against **`q(N)^{unionCallDeg l}`** (the exponent of `GateFreeOK`). Main declarations: `unionCalls_le` (at
`unionSetupS2 l G` for every gate with `p₀ + 6 ≤ A_pad`) and **`setupF_calls_le`** (at `setupF l F`, every `F`), the
form C6's `tr:time` consumes with `Split.calls_absorb`: the calls are at most `q^{unionCallDeg}`, each within a
constant times `callBudget` plus `(q+1)^{c−1}` glue. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.UnionCallCount
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleDepth)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open Filter

/-! ## Pure arithmetic -/

/-- The call count `24K(1+2K(s+1))⁴` against a polynomial bound `K ≤ K₀X` on the PCPP bound. -/
theorem count_arith (K K₀ X s : ℕ) (hK : K ≤ K₀ * X) (hX : 1 ≤ X) :
    24 * K * (1 + 2 * K * (s + 1)) ^ 4 ≤ 24 * K₀ * (1 + 2 * K₀) ^ 4 * X ^ 5 * (s + 1) ^ 4 := by
  have hXs : 1 ≤ X * (s + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 2 * K * (s + 1) ≤ 2 * K₀ * (X * (s + 1)) := by
    calc 2 * K * (s + 1) ≤ 2 * (K₀ * X) * (s + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hK)
      _ = 2 * K₀ * (X * (s + 1)) := by ring
  have h1 : 1 + 2 * K * (s + 1) ≤ (1 + 2 * K₀) * X * (s + 1) := by
    calc 1 + 2 * K * (s + 1) ≤ X * (s + 1) + 2 * K₀ * (X * (s + 1)) := Nat.add_le_add hXs h2
      _ = (1 + 2 * K₀) * X * (s + 1) := by ring
  calc 24 * K * (1 + 2 * K * (s + 1)) ^ 4 ≤ 24 * (K₀ * X) * ((1 + 2 * K₀) * X * (s + 1)) ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hK) (Nat.pow_le_pow_left h1 4)
    _ = 24 * K₀ * (1 + 2 * K₀) ^ 4 * X ^ 5 * (s + 1) ^ 4 := by ring

/-- `(x+1)⁸ ≤ 256(C+1)L³` from `x⁸ ≤ C L³` and `L ≥ 1`. -/
theorem succ_pow8_le (x C L : ℕ) (hx : x ^ 8 ≤ C * L ^ 3) (hL : 1 ≤ L) :
    (x + 1) ^ 8 ≤ 256 * (C + 1) * L ^ 3 := by
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0
    calc (0 + 1) ^ 8 = 1 := by norm_num
      _ ≤ 256 * (C + 1) * L ^ 3 := by nlinarith
  · calc (x + 1) ^ 8 ≤ (2 * x) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      _ = 256 * x ^ 8 := by ring
      _ ≤ 256 * (C * L ^ 3) := Nat.mul_le_mul_left _ hx
      _ ≤ 256 * (C + 1) * L ^ 3 := by nlinarith

/-- **The grid factor is absorbed by one power of `q`**: for every constant `C` and exponent `m`, eventually
`C (q+1)^m (s(q)+1)⁴ ≤ q^{m+1}`, whenever `s(q)⁸ ≤ C_sp L(q)³`. -/
theorem eventually_calls (C m Csp : ℕ) (sp : ℕ → ℕ) (hsp : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3) :
    ∀ᶠ q : ℕ in atTop, C * (q + 1) ^ m * (sp q + 1) ^ 4 ≤ q ^ (m + 1) := by
  filter_upwards [eventually_mul_Lq_pow_le (C ^ 2 * 4 ^ m * (256 * (Csp + 1))) 3, eventually_ge_atTop 1] with q hq hq1
  have h8 := succ_pow8_le (sp q) Csp (Lq q) (hsp q) (Lq_pos q)
  have hsq : (C * 2 ^ m * (sp q + 1) ^ 4) ^ 2 ≤ q ^ 2 := by
    calc (C * 2 ^ m * (sp q + 1) ^ 4) ^ 2 = C ^ 2 * 4 ^ m * (sp q + 1) ^ 8 := by
          rw [show (4 : ℕ) ^ m = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]; ring
      _ ≤ C ^ 2 * 4 ^ m * (256 * (Csp + 1) * Lq q ^ 3) := Nat.mul_le_mul_left _ h8
      _ = C ^ 2 * 4 ^ m * (256 * (Csp + 1)) * Lq q ^ 3 := by ring
      _ ≤ q := hq
      _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have ha : C * 2 ^ m * (sp q + 1) ^ 4 ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq
  have hq2 : (q + 1) ^ m ≤ 2 ^ m * q ^ m := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) m
  calc C * (q + 1) ^ m * (sp q + 1) ^ 4 ≤ C * (2 ^ m * q ^ m) * (sp q + 1) ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq2)
    _ = (C * 2 ^ m * (sp q + 1) ^ 4) * q ^ m := by ring
    _ ≤ q * q ^ m := Nat.mul_le_mul_right _ ha
    _ = q ^ (m + 1) := by rw [pow_succ, mul_comm]

/-! ## The substituted request's size at `σ_H` -/

section Generic
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- `σ_H` meets the three size conditions of `size_arith`. -/
theorem sigmaH_ge (eQ d : ℕ) :
    eQ + 2 ^ oracleDepth d ≤ unionSigmaH eQ d ∧ 3 * eQ ≤ unionSigmaH eQ d ∧ 1 ≤ unionSigmaH eQ d := by
  unfold unionSigmaH
  have h := Nat.one_le_two_pow (n := oracleDepth d)
  refine ⟨le_max_left _ _, le_max_right _ _, ?_⟩
  exact le_trans (by omega) (le_max_left _ _)

/-- **The substituted request's size** for any union setup whose PCP makes at most `C_H (w+1)^{e_Q}` queries, at an
oracle of size `< (w+1)^g`: `size(H) + 1 ≤ K_s (w+1)^σ` for every `σ ≥ e_Q + g, 3e_Q, 1`. -/
theorem requestSize_le_of (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N))
    (CH eQ g σ : ℕ) (hQ : S.pcp.queryCount N ≤ CH * (S.pcp.nativeWidth N + 1) ^ eQ)
    (hos : oracle.size + 1 ≤ (S.pcp.nativeWidth N + 1) ^ g) (h1 : eQ + g ≤ σ) (h3 : 3 * eQ ≤ σ) (h0 : 1 ≤ σ) :
    (S.request z oracle).circuit.size + 1 ≤
      (3 * CH + 24 * CH ^ 3 + S.pcppAlg.minimumArity + 3) * (S.pcp.nativeWidth N + 1) ^ σ := by
  have hreq := PCPPRequestBoundary.request_size S.pcppAlg
    (PCPPSubstitution.compactSubstituted oracle (S.pcp.queryAddressBits z) (S.pcp.decision z fun _ => false))
  have hdom : PCPPRequestBoundary.domain S.pcppAlg (S.pcp.nativeWidth N) ≤
      S.pcp.nativeWidth N + S.pcppAlg.minimumArity := by
    unfold PCPPRequestBoundary.domain; omega
  have key := size_arith _ _ _ _ _ _ _ _ _ _ hQ hos
    (PCPPSubstitution.compactSubstituted_size oracle (S.pcp.queryAddressBits z) (S.pcp.decision z fun _ => false))
    hdom h1 h3 h0
  show (PCPPRequestBoundary.request S.pcppAlg _).circuit.size + 1 ≤ _
  rw [hreq]
  exact key

/-- The request's arity is `max(w, minimumArity)`. -/
theorem request_arity_of (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N)) :
    (S.request z oracle).arity = max (S.pcp.nativeWidth N) S.pcppAlg.minimumArity := rfl

/-- **The count at one setup**, from its three numeric facts: the query bound `C_H (w+1)^{e_Q}`, the grid law
`s⁸ ≤ C_sp L³`, and the width `w(N) = q(N)` eventually with `q(N) → ∞`. Every guess with an oracle within `q^G`
schedules at most `q(N)^{5σ_H d_a + 1}` calls, eventually. -/
theorem calls_le_of (S : UnionSetup I) (qN : ℕ → ℕ) (hqN : Tendsto qN atTop atTop) (CH eQ Csp : ℕ)
    (hQ : ∀ N, S.pcp.queryCount N ≤ CH * (S.pcp.nativeWidth N + 1) ^ eQ)
    (hsp : ∀ q, S.gridSize q ^ 8 ≤ Csp * Lq q ^ 3)
    (hw : ∀ᶠ N in atTop, S.pcp.nativeWidth N = qN N) :
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess S z),
      g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ qN N ^ (5 * unionSigmaH eQ S.G * S.pcppAlg.degree + 1) := by
  obtain ⟨h1, h3, h0⟩ := sigmaH_ge eQ S.G
  set σ := unionSigmaH eQ S.G with hσ
  set d := S.pcppAlg.degree with hd
  set Ks := 3 * CH + 24 * CH ^ 3 + S.pcppAlg.minimumArity + 3 with hKs
  set K₀ := S.pcppAlg.coefficient * Ks ^ d with hK₀
  set C := 24 * K₀ * (1 + 2 * K₀) ^ 4 with hC
  filter_upwards [hw, hqN.eventually (eventually_calls C (σ * d * 5) Csp S.gridSize hsp),
    hqN.eventually (eventually_ge_atTop S.pcppAlg.minimumArity)] with N hwN hbig hmin
  intro z g hsize tr
  have hos := oracleSize_le S.G (S.pcp.nativeWidth N) g.oracle.size hsize
  have hsz := requestSize_le_of S z g.oracle CH eQ _ σ (hQ N) hos h1 h3 h0
  rw [hwN] at hsz
  have hK : S.pcppAlg.coefficient * ((S.request z g.oracle).circuit.size + 1) ^ d ≤ K₀ * ((qN N + 1) ^ (σ * d)) := by
    calc S.pcppAlg.coefficient * ((S.request z g.oracle).circuit.size + 1) ^ d
        ≤ S.pcppAlg.coefficient * (Ks * (qN N + 1) ^ σ) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz d)
      _ = K₀ * (qN N + 1) ^ (σ * d) := by rw [hK₀, mul_pow, ← pow_mul]; ring
  have hX : 1 ≤ (qN N + 1) ^ (σ * d) := Nat.one_le_pow _ _ (by omega)
  have hs : g.s = S.gridSize (qN N) := by
    show S.gridSize (S.request z g.oracle).arity = S.gridSize (qN N)
    rw [request_arity_of, hwN, max_eq_left hmin]
  have hlen := length_schedule_le g tr
  have har := count_arith _ K₀ _ g.s hK hX
  rw [hs] at har
  calc (g.checkData tr).schedule.length ≤ _ := hlen
    _ ≤ C * ((qN N + 1) ^ (σ * d)) ^ 5 * (S.gridSize (qN N) + 1) ^ 4 := by rw [hs]; exact har
    _ = C * (qN N + 1) ^ (σ * d * 5) * (S.gridSize (qN N) + 1) ^ 4 := by rw [← pow_mul]
    _ ≤ qN N ^ (σ * d * 5 + 1) := hbig
    _ = qN N ^ (5 * σ * d + 1) := by ring_nf

end Generic

/-! ## At the pinned setup `S₂` -/

section Pinned
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The hierarchy PCP's query bound at any width above its own. -/
theorem hierQuery_le (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))) (N w : ℕ)
    (hw : (hierarchyPCP l H).data.pcp.nativeWidth N ≤ w) :
    (hierarchyPCP l H).data.pcp.queryCount N ≤
      (hierarchyPCP l H).data.coefficient * (w + 1) ^ (gateSource l).degrees.queries :=
  ((hierarchyPCP l H).data.queryBound N).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

/-- `S₂` off the recovered language is `S₁`. -/
theorem unionSetupS2_ne (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) (h : L ≠ recL l kclk) :
    unionSetupS2 l G kclk coef A a ha L hL = unionSetupS1 l G kclk coef A a ha L hL := by
  unfold unionSetupS2
  rw [dif_neg h]

/-- **The union's call count at `S₂`**: for every gate with `p₀ + 6 ≤ A_pad`, every language of the clock, eventually
in `N`, every guess whose oracle is within `q^G` schedules at most `q(N)^{unionCallDeg l}` primitive calls, where
`q(N)` is the ledger's native width. -/
theorem unionCalls_le (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (unionSetupS2 l G kclk coef A a ha L hL) z),
      g.oracle.size ≤ oracleSizeBound (unionSetupS2 l G kclk coef A a ha L hL).G
        ((unionSetupS2 l G kclk coef A a ha L hL).pcp.nativeWidth N) → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ (G.budget kclk coef A a ha).q N ^ Split.unionCallDeg l := by
  have hq : Tendsto (G.budget kclk coef A a ha).q atTop atTop := tendsto_nativeWidth kclk G.Apad
  by_cases h : L = recL l kclk
  · subst h
    rw [unionSetupS2_recL l G kclk coef A a ha hL]
    obtain ⟨N₀, hN₀⟩ := recSetup2_width l G kclk coef A a ha hApad
    exact calls_le_of (recSetup2 l G kclk coef A a ha) _ hq _ (gateSource l).degrees.queries G.row.Csp
      (fun N => hierQuery_le l kclk (refH l kclk) N _ (le_max_left _ _)) G.row.sp_le
      (eventually_atTop.2 ⟨N₀, hN₀⟩)
  · rw [unionSetupS2_ne l G kclk coef A a ha L hL h]
    obtain ⟨N₀, hN₀⟩ := unionSetupS1_width l G kclk coef A a ha L hL hApad
    exact calls_le_of (unionSetupS1 l G kclk coef A a ha L hL) _ hq _ (gateSource l).degrees.queries G.row.Csp
      (fun N => hierQuery_le l kclk (hierarchyOf hL) N _ (le_max_left _ _)) G.row.sp_le
      (eventually_atTop.2 ⟨N₀, hN₀⟩)

/-- **The forcing lemma at the concrete gate**: at `setupF l F`, for every choice `F` of the free
constants, every clock, coefficient, source work and language, eventually in `N`, every guess whose oracle is within
`q^G` schedules at most `q(N)^{unionCallDeg l}` calls, `q(N)` the budget's width. With `GateFreeOK` and
`Split.calls_absorb` this bounds the calls' total time by `q(N)^{callDeg}` times the per-call cost's constant, for any
per-call glue within `K (q+1)^{callDegMargin − 1}`. -/
theorem setupF_calls_le (F : Split.GateFree l) (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (Split.setupF l F kclk coef A a ha L hL) z),
      g.oracle.size ≤ oracleSizeBound (Split.setupF l F kclk coef A a ha L hL).G
        ((Split.setupF l F kclk coef A a ha L hL).pcp.nativeWidth N) → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ ((Split.gate0 l F).budget kclk coef A a ha).q N ^ Split.unionCallDeg l :=
  unionCalls_le l (Split.gate0 l F) kclk coef A a ha (Split.gateRel_gate0 l F).apad L hL

end Pinned

end NearCubicWires.WireExponent3_5.Transfer.UnionCallCount
