import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.UnionMachine.FrontLedger
import Proof.Wire_3_5.UnionMachine.FrontOutRef
import Proof.Wire_3_5.UnionMachine.UnionCallCount

/-! # C6 front, F2: the table's sizes and the capacities at the pinned setup (P3:3622, 3669-3691, 3797-3811)

What the schedule loop's hypotheses (`LoopHyps`) and the per-call budget need from the front's valid branch, uniformly
in the witness, eventually in `N`, at the pinned setup `S₂` (`Split.setupF`, `PlanW2.SUE`):
* the setup's grid and width: `S2_gridSize` (`s(q) = sp(q)`), `S2_gridMass` with `gridMassOf_le` (`Λ̄(q) ≤ s(q)`),
  `S2_width` (the padded width is the ledger's `q(N)` eventually), `gridFacts_SUE` (`Λ̄ ≥ 1` natural, `s ≥ 1`);
* the PCPP's clause count `2^{clauseBits} ≤ K₀(q+1)^{D₀}` (`clause_le_of`, `S2_clause`; the substituted circuit's size, as
  in `calls_le_of`);
* every term's scaled coefficient `|c·s⁴| ≤ 2(Λ̄+s)⁴` (`BdForm`, `coeff_scaled_abs`, `CheckB.terms_mag`; `c = κ_j∏F`,
  `|κ_j| ≤ 2`, every factor `|F|·s ≤ Λ̄ + s` since the grid signs are in `{−1,0,1}`), every request at `q`
  (`CheckB.terms_n`), the table's entries (`mem_tableAll`), the accumulators' start (`accStart_le`);
* `PQ` (polynomials in `q`, tactic `c6pq`), `needCap`, **`valid_atoms_of`** (from generic setup facts, eventually: `p =
  unionBits q`, requests at `q`, magnitudes, words, table length, accumulators' start within polynomials);
* the approved capacities `capQ q = (32·coef+1)·2^{q−⌊k/4⌋}·(q+1)^{A_main}`, `RQ q = 1000(q+6)·capQ q`,
  `KfC = 2·10⁶·2^{A_main}`: `capQ_le` (`cap + 1 ≤ 34·2^{A_main}·callBudget q`), **`good_facts`** (the valid branch meets
  `LoopHyps`, fits its accumulators, and each loop step is within `KfC·(q+1)^{c−1}·callBudget`), **`outRef_fields`**
  (FrontAtW3's `loop`, `accFit`, `perCall`, `capAcc` for the front's reference output at these capacities).

Paper quantity of the main type: the call table's entries and the loop's capacities (P3:3485-3491, 3669-3691, 3797-3811). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleDepth)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open Filter

/-! ## The pinned setup's grid and width -/

section Setup
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
  (hL : InNTIME (fun n => n ^ (kclk + 2)) L)

theorem S2_gridSize : (unionSetupS2 l G kclk coef A a ha L hL).gridSize = G.row.sp := by
  by_cases h : L = recL l kclk
  · subst h; rw [unionSetupS2_recL]; rfl
  · rw [UnionCallCount.unionSetupS2_ne l G kclk coef A a ha L hL h]; rfl

theorem S2_gridMass : (unionSetupS2 l G kclk coef A a ha L hL).gridMass = gridMassOf (gateCδ1 l) G.row.sp := by
  by_cases h : L = recL l kclk
  · subst h; rw [unionSetupS2_recL]; rfl
  · rw [UnionCallCount.unionSetupS2_ne l G kclk coef A a ha L hL h]; rfl

theorem gridMassOf_le (Cδ : ℕ) (sp : ℕ → ℕ) (q : ℕ) : gridMassOf Cδ sp q ≤ (sp q : ℚ) := by
  unfold gridMassOf
  have h1 : Nat.sqrt (sp q / Cδ) ≤ sp q := (Nat.sqrt_le_self _).trans (Nat.div_le_self _ _)
  exact_mod_cast h1

theorem S2_width (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∀ᶠ N in atTop, (unionSetupS2 l G kclk coef A a ha L hL).pcp.nativeWidth N = (G.budget kclk coef A a ha).q N := by
  by_cases h : L = recL l kclk
  · subst h
    rw [unionSetupS2_recL]
    obtain ⟨N₀, hN₀⟩ := recSetup2_width l G kclk coef A a ha hApad
    exact eventually_atTop.2 ⟨N₀, hN₀⟩
  · rw [UnionCallCount.unionSetupS2_ne l G kclk coef A a ha L hL h]
    obtain ⟨N₀, hN₀⟩ := unionSetupS1_width l G kclk coef A a ha L hL hApad
    exact eventually_atTop.2 ⟨N₀, hN₀⟩

end Setup

/-! ## The clause count -/

section Clause
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **The PCPP's clause count at one setup** (the first half of `calls_le_of`): from the PCP's query bound
and the width `w(N) = q(N)` eventually, every guess with an oracle within `q^G` has `2^{clauseBits} ≤ K₀(q+1)^{D₀}`. -/
theorem clause_le_of (S : UnionSetup I) (qN : ℕ → ℕ) (CH eQ : ℕ)
    (hQ : ∀ N, S.pcp.queryCount N ≤ CH * (S.pcp.nativeWidth N + 1) ^ eQ)
    (hw : ∀ᶠ N in atTop, S.pcp.nativeWidth N = qN N) :
    ∃ K₀ D₀ : ℕ, ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess S z),
      g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) → ∀ tr : List ℕ,
        2 ^ (g.checkData tr).pcpp.clauseBits ≤ K₀ * (qN N + 1) ^ D₀ := by
  obtain ⟨h1, h3, h0⟩ := UnionCallCount.sigmaH_ge eQ S.G
  refine ⟨S.pcppAlg.coefficient * (3 * CH + 24 * CH ^ 3 + S.pcppAlg.minimumArity + 3) ^ S.pcppAlg.degree,
    unionSigmaH eQ S.G * S.pcppAlg.degree, ?_⟩
  filter_upwards [hw] with N hwN
  intro z g hsize tr
  have hos := oracleSize_le S.G (S.pcp.nativeWidth N) g.oracle.size hsize
  have hsz := UnionCallCount.requestSize_le_of S z g.oracle CH eQ _ (unionSigmaH eQ S.G) (hQ N) hos h1 h3 h0
  rw [hwN] at hsz
  have hM : 2 ^ (g.checkData tr).pcpp.clauseBits ≤
      S.pcppAlg.coefficient * ((S.request z g.oracle).circuit.size + 1) ^ S.pcppAlg.degree :=
    S.pcppAlg.clauseCountBound (S.request z g.oracle)
  calc 2 ^ (g.checkData tr).pcpp.clauseBits ≤ _ := hM
    _ ≤ S.pcppAlg.coefficient * ((3 * CH + 24 * CH ^ 3 + S.pcppAlg.minimumArity + 3) *
          (qN N + 1) ^ unionSigmaH eQ S.G) ^ S.pcppAlg.degree :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz _)
    _ = S.pcppAlg.coefficient * (3 * CH + 24 * CH ^ 3 + S.pcppAlg.minimumArity + 3) ^ S.pcppAlg.degree *
          (qN N + 1) ^ (unionSigmaH eQ S.G * S.pcppAlg.degree) := by
        rw [mul_pow, ← pow_mul]; ring

end Clause

section ClauseS2
variable (l : Literals) (G : Split.Gate) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
  (hL : InNTIME (fun n => n ^ (kclk + 2)) L)

/-- **The clause count at `S₂`.** -/
theorem S2_clause (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∃ K₀ D₀ : ℕ, ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (unionSetupS2 l G kclk coef A a ha L hL) z),
      g.oracle.size ≤ oracleSizeBound (unionSetupS2 l G kclk coef A a ha L hL).G
        ((unionSetupS2 l G kclk coef A a ha L hL).pcp.nativeWidth N) → ∀ tr : List ℕ,
        2 ^ (g.checkData tr).pcpp.clauseBits ≤ K₀ * ((G.budget kclk coef A a ha).q N + 1) ^ D₀ := by
  by_cases h : L = recL l kclk
  · subst h
    rw [unionSetupS2_recL]
    obtain ⟨N₀, hN₀⟩ := recSetup2_width l G kclk coef A a ha hApad
    exact clause_le_of (recSetup2 l G kclk coef A a ha) _ _ (gateSource l).degrees.queries
      (fun N => UnionCallCount.hierQuery_le l kclk (refH l kclk) N _ (le_max_left _ _)) (eventually_atTop.2 ⟨N₀, hN₀⟩)
  · rw [UnionCallCount.unionSetupS2_ne l G kclk coef A a ha L hL h]
    obtain ⟨N₀, hN₀⟩ := unionSetupS1_width l G kclk coef A a ha L hL hApad
    exact clause_le_of (unionSetupS1 l G kclk coef A a ha L hL) _ _ (gateSource l).degrees.queries
      (fun N => UnionCallCount.hierQuery_le l kclk (hierarchyOf hL) N _ (le_max_left _ _))
      (eventually_atTop.2 ⟨N₀, hN₀⟩)

end ClauseS2

/-! ## The scaled coefficients' size -/

section Mag
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge

/-- A form whose values times `s` are at most `K` in absolute value. -/
def BdForm {α : Type} (s K : ℕ) (w : α → ℚ) : Prop := ∀ a, |w a| * (s : ℚ) ≤ (K : ℚ)

/-- **Scaled coefficients are small**: `|κ_j| ≤ 2` and every factor within `K` give `|c·s⁴| ≤ 2K⁴`. -/
theorem coeff_scaled_abs {α : Type} (s K : ℕ) (P : Poly4Q α) (hκ : ∀ j, |P.κ j| ≤ 2)
    (hF : ∀ j k, BdForm s K (P.F j k)) (j : Fin 4) (t : Fin 4 → α) :
    |P.coeff j t * (s : ℚ) ^ 4| ≤ 2 * (K : ℚ) ^ 4 := by
  unfold Poly4Q.coeff
  rw [Fin.prod_univ_four]
  have e : |P.κ j * (P.F j 0 (t 0) * P.F j 1 (t 1) * P.F j 2 (t 2) * P.F j 3 (t 3)) * (s : ℚ) ^ 4| =
      |P.κ j| * ((|P.F j 0 (t 0)| * s) * (|P.F j 1 (t 1)| * s) * (|P.F j 2 (t 2)| * s) *
        (|P.F j 3 (t 3)| * s)) := by
    simp only [abs_mul, abs_pow, Nat.abs_cast]; ring
  rw [e]
  have h0 := hF j 0 (t 0)
  have h1 := hF j 1 (t 1)
  have h2 := hF j 2 (t 2)
  have h3 := hF j 3 (t 3)
  have hk := hκ j
  calc |P.κ j| * ((|P.F j 0 (t 0)| * s) * (|P.F j 1 (t 1)| * s) * (|P.F j 2 (t 2)| * s) * (|P.F j 3 (t 3)| * s))
      ≤ 2 * ((K : ℚ) * K * K * K) := by gcongr
    _ = 2 * (K : ℚ) ^ 4 := by ring

namespace CheckB
variable (D : UnionCheckData)

theorem sign_abs (hsg : D.signsOk = true) (Y : PcppVar D.pcpp) (b : Fin D.s) : |(D.sign Y b : ℚ)| ≤ 1 := by
  have h := of_decide_eq_true hsg Y b
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> rw [h] <;> norm_num

theorem wS_bd (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (hsg : D.signsOk = true) (X : PcppVar D.pcpp) :
    BdForm D.s (Λ + D.s) (D.wS X) := by
  intro a
  have hs0 : (0 : ℚ) < D.s := by exact_mod_cast hs
  rcases a with u | (⟨Y, b⟩ | Y)
  · simp [UnionCheckData.wS] <;> positivity
  · by_cases h : Y = X
    · subst h
      simp only [UnionCheckData.wS, ↓reduceIte, hm]
      have hb := sign_abs D hsg Y b
      have e : |(Λ : ℚ) / D.s * (D.sign Y b : ℚ)| * D.s = Λ * |(D.sign Y b : ℚ)| := by
        rw [abs_mul, abs_div, Nat.abs_cast, Nat.abs_cast]; field_simp
      rw [e]
      have hΛ : (0 : ℚ) ≤ Λ := Nat.cast_nonneg Λ
      calc (Λ : ℚ) * |(D.sign Y b : ℚ)| ≤ Λ * 1 := by gcongr
        _ ≤ ((Λ + D.s : ℕ) : ℚ) := by push_cast; linarith
    · simp [UnionCheckData.wS, h] <;> positivity
  · simp [UnionCheckData.wS] <;> positivity

theorem wOne_bd (Λ : ℕ) : BdForm D.s (Λ + D.s) D.wOne := by
  intro a
  rcases a with u | (p | Y)
  · simp [UnionCheckData.wOne] <;> positivity
  · simp [UnionCheckData.wOne] <;> positivity
  · simp [UnionCheckData.wOne] <;> positivity

theorem wE_bd (Λ : ℕ) (X : PcppVar D.pcpp) : BdForm D.s (Λ + D.s) (D.wE X) := by
  intro a
  rcases a with u | (p | Y)
  · simp [UnionCheckData.wE] <;> positivity
  · simp [UnionCheckData.wE] <;> positivity
  · by_cases h : Y = X
    · simp [UnionCheckData.wE, h] <;> positivity
    · simp [UnionCheckData.wE, h] <;> positivity

theorem polyV_abs (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (hsg : D.signsOk = true)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (j : Fin 4) (t : Fin 4 → D.AtomIx) :
    |(D.polyVAt pos).coeff j t * (D.s : ℚ) ^ 4| ≤ 2 * ((Λ + D.s : ℕ) : ℚ) ^ 4 := by
  refine coeff_scaled_abs D.s (Λ + D.s) _ ?_ ?_ j t
  · intro j; unfold UnionCheckData.polyVAt polyVQ
    split_ifs <;> fin_cases j <;> norm_num
  · intro j k; unfold UnionCheckData.polyVAt polyVQ
    have hS := wS_bd D Λ hm hs hsg (posVar D.pcpp pos.1 pos.2)
    have hO := wOne_bd D Λ
    have hE := wE_bd D Λ (posVar D.pcpp pos.1 pos.2)
    split_ifs <;> fin_cases j <;> fin_cases k <;> simpa

theorem polyQ_abs (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (hsg : D.signsOk = true)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (j : Fin 4) (t : Fin 4 → D.AtomIx) :
    |(D.polyQAt pos).coeff j t * (D.s : ℚ) ^ 4| ≤ 2 * ((Λ + D.s : ℕ) : ℚ) ^ 4 := by
  refine coeff_scaled_abs D.s (Λ + D.s) _ ?_ ?_ j t
  · intro j; unfold UnionCheckData.polyQAt polyQQ
    fin_cases j <;> norm_num
  · intro j k; unfold UnionCheckData.polyQAt polyQQ
    have hS := wS_bd D Λ hm hs hsg (posVar D.pcpp pos.1 pos.2)
    have hO := wOne_bd D Λ
    fin_cases j <;> fin_cases k <;> simpa

theorem polyMu_abs (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (hsg : D.signsOk = true)
    (i : Fin (2 ^ D.pcpp.clauseBits)) (j : Fin 4) (t : Fin 4 → D.AtomIx) :
    |(D.polyMuAt i).coeff j t * (D.s : ℚ) ^ 4| ≤ 2 * ((Λ + D.s : ℕ) : ℚ) ^ 4 := by
  refine coeff_scaled_abs D.s (Λ + D.s) _ ?_ ?_ j t
  · intro j; unfold UnionCheckData.polyMuAt polyMuQ
    generalize posNeg D.pcpp i 0 = n0
    generalize posNeg D.pcpp i 1 = n1
    cases n0 <;> cases n1 <;> fin_cases j <;> norm_num [litAQ, litBQ]
  · intro j k; unfold UnionCheckData.polyMuAt polyMuQ
    have hX := wS_bd D Λ hm hs hsg (posVar D.pcpp i 0)
    have hY := wS_bd D Λ hm hs hsg (posVar D.pcpp i 1)
    have hO := wOne_bd D Λ
    fin_cases j <;> fin_cases k <;> simpa

/-- **Every term's scaled coefficient is at most `2(Λ̄+s)⁴`**, as a natural number. -/
theorem terms_mag (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (hsg : D.signsOk = true) (t : ℚ × PrimRequest)
    (ht : t ∈ D.termsV ∨ t ∈ D.termsQ ∨ t ∈ D.termsMu) :
    (scaledZ D.s t.1).natAbs ≤ 2 * (Λ + D.s) ^ 4 := by
  have hq : |t.1 * (D.s : ℚ) ^ 4| ≤ 2 * ((Λ + D.s : ℕ) : ℚ) ^ 4 ∧ IsIntQ (t.1 * (D.s : ℚ) ^ 4) := by
    rcases ht with ht | ht | ht
    · obtain ⟨pos, j, u, -, rfl⟩ := (D.mem_termsV t).1 ht
      exact ⟨polyV_abs D Λ hm hs hsg pos j u, CheckData.polyV_int D Λ hm hs pos j u⟩
    · obtain ⟨pos, j, u, -, rfl⟩ := (D.mem_termsQ t).1 ht
      exact ⟨polyQ_abs D Λ hm hs hsg pos j u, CheckData.polyQ_int D Λ hm hs pos j u⟩
    · obtain ⟨i, j, u, -, rfl⟩ := (D.mem_termsMu t).1 ht
      exact ⟨polyMu_abs D Λ hm hs hsg i j u, CheckData.polyMu_int D Λ hm hs i j u⟩
  have e := hq.2.num_eq
  have h2 : ((scaledZ D.s t.1).natAbs : ℚ) ≤ ((2 * (Λ + D.s) ^ 4 : ℕ) : ℚ) := by
    have e2 : ((scaledZ D.s t.1).natAbs : ℚ) = |t.1 * (D.s : ℚ) ^ 4| := by
      rw [Nat.cast_natAbs, Int.cast_abs]; unfold scaledZ; rw [e]
    rw [e2]
    have h3 := hq.1
    push_cast at h3 ⊢
    exact h3
  exact_mod_cast h2

/-- The terms' requests are at the check data's arity. -/
theorem terms_n (t : ℚ × PrimRequest) (ht : t ∈ D.termsV ∨ t ∈ D.termsQ ∨ t ∈ D.termsMu) : t.2.n = D.q := by
  rcases ht with ht | ht | ht
  · obtain ⟨pos, j, u, -, rfl⟩ := (D.mem_termsV t).1 ht; rfl
  · obtain ⟨pos, j, u, -, rfl⟩ := (D.mem_termsQ t).1 ht; rfl
  · obtain ⟨i, j, u, -, rfl⟩ := (D.mem_termsMu t).1 ht; rfl

end CheckB

end Mag

/-! ## The table's entries -/

section Entries
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

theorem mem_tableAll (s : ℕ) (TV TQ TM : List (ℚ × PrimRequest)) (hV : ∀ t ∈ TV, I.Call t.2)
    (hQ : ∀ t ∈ TQ, I.Call t.2) (hM : ∀ t ∈ TM, I.Call t.2) (x : Sched.TEntry I)
    (hx : x ∈ tableAll s TV TQ TM hV hQ hM) :
    ∃ (k : Fin 3) (t : ℚ × PrimRequest), (t ∈ TV ∨ t ∈ TQ ∨ t ∈ TM) ∧ x.e = entryOf k s t ∧ x.req.1 = t.2 := by
  unfold tableAll tableOfTerms at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨t, ht, rfl⟩ := List.mem_pmap.1 hx
      exact ⟨0, t, Or.inl ht, rfl, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := List.mem_pmap.1 hx
      exact ⟨1, t, Or.inr (Or.inl ht), rfl, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_pmap.1 hx
    exact ⟨2, t, Or.inr (Or.inr ht), rfl, rfl⟩

theorem foldr_max_le (l : List ℕ) (b : ℕ) (h : ∀ a ∈ l, a ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldr_cons]
    exact max_le (h c List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem c ha))

end Entries

/-! ## The accumulators' start -/

section Acc
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

theorem floor_natAbs_le (x : ℚ) (Z : ℕ) (h : |x| ≤ Z) : (⌊x⌋).natAbs ≤ Z + 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 : |(⌊x⌋ : ℚ)| ≤ Z + 1 := by
    rw [abs_le] at h ⊢; constructor <;> linarith [h.1, h.2]
  have h4 : ((⌊x⌋).natAbs : ℚ) ≤ Z + 1 := by rw [Nat.cast_natAbs, Int.cast_abs]; exact h3
  exact_mod_cast h4

theorem ceil_natAbs_le (x : ℚ) (Z : ℕ) (h : |x| ≤ Z) : (⌈x⌉).natAbs ≤ Z + 1 := by
  have h1 := Int.le_ceil x
  have h2 := Int.ceil_lt_add_one x
  have h3 : |(⌈x⌉ : ℚ)| ≤ Z + 1 := by
    rw [abs_le] at h ⊢; constructor <;> linarith [h.1, h.2]
  have h4 : ((⌈x⌉).natAbs : ℚ) ≤ Z + 1 := by rw [Nat.cast_natAbs, Int.cast_abs]; exact h3
  exact_mod_cast h4

theorem threshAcc_le (TV TQ TM : ℤ) (Z : ℕ) (hV : TV.natAbs ≤ Z) (hQ : TQ.natAbs ≤ Z) (hM : TM.natAbs ≤ Z)
    (i : Fin 6) : threshAcc TV TQ TM i ≤ Z := by
  fin_cases i <;> simp only [threshAcc, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
    Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] <;> omega

/-- The masked verifier's constants, rounded up: `⌈|v₀|⌉ + ⌈|τ|⌉ + 1`. -/
noncomputable def vcOf (S : UnionSetup I) : ℕ := ⌈|S.params.v0|⌉₊ + ⌈|S.params.threshold|⌉₊ + 1

/-- **The accumulators' start is at most `s⁴·2^p·2^{clauseBits+1}·(2V + (1+Λ̄)⁴) + 1`.** -/
theorem accStart_le (S : UnionSetup I) (D : UnionCheckData) (p Λ : ℕ) (hm : D.mass = Λ) (i : Fin 6) :
    FrontOutRef.accStart S D p i ≤ D.s ^ 4 * 2 ^ p * (2 ^ D.pcpp.clauseBits * 2) * (2 * vcOf S + (1 + Λ) ^ 4) + 1 := by
  set Z := D.s ^ 4 * 2 ^ p * (2 ^ D.pcpp.clauseBits * 2) * (2 * vcOf S + (1 + Λ) ^ 4) with hZ
  have hδ0 : 0 ≤ slackOf D.mass p := by unfold slackOf; rw [hm]; positivity
  have hδ : slackOf D.mass p ≤ ((1 + Λ) ^ 4 : ℕ) := by
    unfold slackOf; rw [hm]; push_cast
    have h1 : (1 : ℚ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    exact div_le_self (by positivity) h1
  have hv := Nat.le_ceil |S.params.v0|
  have ht := Nat.le_ceil |S.params.threshold|
  have hvc : (|S.params.v0| + |S.params.threshold| + 1 : ℚ) ≤ vcOf S := by unfold vcOf; push_cast; linarith
  have hscale : 0 ≤ scaleVQ D p := by unfold scaleVQ; positivity
  have hscaleM : 0 ≤ scaleMu D p := by unfold scaleMu; positivity
  have hMV : scaleMu D p ≤ scaleVQ D p := by
    unfold scaleMu scaleVQ
    have : (0 : ℚ) ≤ (D.s : ℚ) ^ 4 * 2 ^ p * 2 ^ D.pcpp.clauseBits := by positivity
    nlinarith
  have hZq : scaleVQ D p * (2 * vcOf S + (1 + Λ) ^ 4) = (Z : ℚ) := by rw [hZ]; unfold scaleVQ; push_cast; ring
  have hY : ∀ y : ℚ, |y| ≤ 2 * vcOf S + (1 + Λ) ^ 4 → ∀ c : ℚ, 0 ≤ c → c ≤ scaleVQ D p → |c * y| ≤ Z := by
    intro y hy c hc0 hc
    rw [abs_mul, abs_of_nonneg hc0, ← hZq]
    have hpos : (0 : ℚ) ≤ 2 * vcOf S + (1 + Λ) ^ 4 := by positivity
    calc c * |y| ≤ scaleVQ D p * |y| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ ≤ scaleVQ D p * (2 * vcOf S + (1 + Λ) ^ 4) := mul_le_mul_of_nonneg_left hy hscale
  have hδ' : slackOf D.mass p ≤ (1 + Λ) ^ 4 := by exact_mod_cast hδ
  have y1 : |2 * S.params.v0 + slackOf D.mass p| ≤ 2 * vcOf S + (1 + Λ) ^ 4 := by
    rw [abs_le] at *; constructor <;> linarith [abs_nonneg S.params.v0, le_abs_self S.params.v0,
      neg_abs_le S.params.v0, abs_nonneg S.params.threshold]
  have y2 : |1 + S.params.v0 + slackOf D.mass p| ≤ 2 * vcOf S + (1 + Λ) ^ 4 := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg S.params.v0, le_abs_self S.params.v0,
      neg_abs_le S.params.v0, abs_nonneg S.params.threshold]
  have y3 : |S.params.threshold - slackOf D.mass p| ≤ 2 * vcOf S + (1 + Λ) ^ 4 := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg S.params.threshold, le_abs_self S.params.threshold,
      neg_abs_le S.params.threshold, abs_nonneg S.params.v0]
  have t1 := floor_natAbs_le _ Z (hY _ y1 _ hscale le_rfl)
  have t2 := floor_natAbs_le _ Z (hY _ y2 _ hscale le_rfl)
  have t3 := ceil_natAbs_le _ Z (hY _ y3 _ hscaleM hMV)
  exact threshAcc_le _ _ _ (Z + 1) t1 t2 t3 i

end Acc

/-! ## Polynomials in `q` -/

section PQ

/-- `f` is at most `c·(q+1)^d`. -/
def PQ (f : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ q, f q ≤ c * (q + 1) ^ d

theorem PQ.const (c : ℕ) : PQ fun _ => c := ⟨c, 0, fun q => by simp⟩

theorem PQ.var : PQ fun q => q := ⟨1, 1, fun q => by simp⟩

theorem PQ.add {f g : ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ fun q => f q + g q := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, max d1 d2, fun q => ?_⟩
  have e1 := Nat.mul_le_mul_left c1 (Nat.pow_le_pow_right (by omega : 1 ≤ q + 1) (le_max_left d1 d2))
  have e2 := Nat.mul_le_mul_left c2 (Nat.pow_le_pow_right (by omega : 1 ≤ q + 1) (le_max_right d1 d2))
  have := h1 q
  have := h2 q
  show f q + g q ≤ _
  rw [Nat.add_mul]
  omega

theorem PQ.mul {f g : ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ fun q => f q * g q := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun q => ?_⟩
  calc f q * g q ≤ (c1 * (q + 1) ^ d1) * (c2 * (q + 1) ^ d2) := Nat.mul_le_mul (h1 q) (h2 q)
    _ = c1 * c2 * (q + 1) ^ (d1 + d2) := by rw [pow_add]; ring

theorem PQ.pow {f : ℕ → ℕ} (hf : PQ f) (n : ℕ) : PQ fun q => f q ^ n := by
  obtain ⟨c, d, h⟩ := hf
  refine ⟨c ^ n, d * n, fun q => ?_⟩
  calc f q ^ n ≤ (c * (q + 1) ^ d) ^ n := Nat.pow_le_pow_left (h q) n
    _ = c ^ n * (q + 1) ^ (d * n) := by rw [mul_pow, pow_mul]

/-- Decompose a polynomial expression in `q`. -/
syntax "c6pq" : tactic
macro_rules
  | `(tactic| c6pq) => `(tactic| first
      | with_reducible assumption
      | with_reducible exact PQ.const _
      | with_reducible exact PQ.var
      | ((with_reducible refine PQ.add ?_ ?_) <;> c6pq)
      | ((with_reducible refine PQ.mul ?_ ?_) <;> c6pq)
      | ((with_reducible refine PQ.pow ?_ _) <;> c6pq))

end PQ

/-! ## The valid branch's sizes, eventually -/

section Bounds

/-- The grid's bound `C_sp·(q+1)³` (`s(q)⁸ ≤ C_sp L³`). -/
def SB (Csp q : ℕ) : ℕ := Csp * (q + 1) ^ 3

/-- The magnitudes' bound `2·(2·SB)⁴`. -/
def MB (Csp q : ℕ) : ℕ := 2 * (SB Csp q + SB Csp q) ^ 4

/-- The accumulators' start bound. -/
def AB (Csp K₀ D₀ V q : ℕ) : ℕ :=
  SB Csp q ^ 4 * (4 * (q + 1)) * (K₀ * (q + 1) ^ D₀ * 2) * (2 * V + (1 + SB Csp q) ^ 4) + 1

/-- **Everything the capacity must exceed besides `8·callBudget`.** -/
def needCap (Csp K₀ D₀ V wc wd ucd q : ℕ) : ℕ :=
  2 * (wc * (q + 1) ^ wd) + MB Csp q + 2 + (8 * (4 * (q + 1)) + 32) +
    (AB Csp K₀ D₀ V q + ((q + 1) ^ ucd + 2) * (MB Csp q * (8 * (4 * (q + 1))))) +
    40 * (MB Csp q + wc * (q + 1) ^ wd + 2) + MB Csp q * (160 * (4 * (q + 1)) + 11) + 100 * (4 * (q + 1)) + 2200

theorem needCap_pq (Csp K₀ D₀ V wc wd ucd : ℕ) : PQ (needCap Csp K₀ D₀ V wc wd ucd) := by
  unfold needCap MB AB SB
  c6pq

theorem two_pow_unionBits (q : ℕ) : 2 ^ unionBits q ≤ 4 * (q + 1) := by
  unfold unionBits
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < q + 2 by omega)
  have hpos : 1 ≤ Nat.clog 2 (q + 2) := Nat.clog_pos (by norm_num) (by omega)
  have e : 2 ^ Nat.clog 2 (q + 2) = 2 * 2 ^ (Nat.clog 2 (q + 2)).pred := by
    rw [← pow_succ']; congr 1
  omega

theorem unionBits_le (q : ℕ) : unionBits q ≤ q + 1 := by
  unfold unionBits
  exact Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := q + 1)
    rw [pow_succ] at this ⊢; omega)

theorem sp_le_SB (Csp : ℕ) (sp : ℕ → ℕ) (hsp : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3) (q : ℕ) : sp q ≤ SB Csp q := by
  unfold SB
  have h1 : sp q ≤ sp q ^ 8 := by
    rcases Nat.eq_zero_or_pos (sp q) with h | h
    · rw [h]; simp
    · exact Nat.le_self_pow (by norm_num) _
  have h2 : Lq q ≤ q + 1 := by
    unfold Lq
    exact Nat.clog_le_of_le_pow (by
      have := Nat.lt_two_pow_self (n := q + 1)
      rw [pow_succ] at this ⊢; omega)
  have h3 : Csp * Lq q ^ 3 ≤ Csp * (q + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 3)
  exact h1.trans ((hsp q).trans h3)

end Bounds

/-! ## The valid branch's atoms, eventually -/

section Atoms
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
open NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **The valid branch's sizes**, from the setup's numeric facts: past a threshold, at every guess passing the front's
checks, the rounding precision is `unionBits q`, every entry's request is at `q`, the magnitudes, words, table length
and accumulators' start are within the polynomial bounds. -/
theorem valid_atoms_of (S : UnionSetup I) (hF : GridFacts S) (sp : ℕ → ℕ) (Csp : ℕ)
    (hsp : ∀ q, sp q ^ 8 ≤ Csp * Lq q ^ 3) (hgs : S.gridSize = sp) (hgm : ∀ q, S.gridMass q ≤ (sp q : ℚ))
    (qN : ℕ → ℕ) (hq : Tendsto qN atTop atTop) (hw : ∀ᶠ N in atTop, S.pcp.nativeWidth N = qN N) (K₀ D₀ : ℕ)
    (hcl : ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess S z),
      g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) → ∀ tr : List ℕ,
        2 ^ (g.checkData tr).pcpp.clauseBits ≤ K₀ * (qN N + 1) ^ D₀)
    (ucd : ℕ) (hcalls : ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess S z),
      g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ qN N ^ ucd)
    (wc wd : ℕ) (hword : ∀ r : PrimRequest, I.Call r → r.word.length ≤ wc * (r.n + 1) ^ wd) :
    ∀ᶠ N in atTop, ∀ (x : BitInput N) (g : UnionGuess S x) (hg : GoodG S g),
      1 ≤ qN N ∧ (goodOut S hF g hg.2.2.2 0 0 0).p = unionBits (qN N) ∧
      (∀ t ∈ (goodOut S hF g hg.2.2.2 0 0 0).table, t.req.1.n = qN N) ∧
      (goodOut S hF g hg.2.2.2 0 0 0).Mm ≤ MB Csp (qN N) ∧
      (goodOut S hF g hg.2.2.2 0 0 0).Wm ≤ wc * (qN N + 1) ^ wd ∧
      (goodOut S hF g hg.2.2.2 0 0 0).table.length ≤ (qN N + 1) ^ ucd ∧
      ∀ i, (goodOut S hF g hg.2.2.2 0 0 0).acc0 i ≤ AB Csp K₀ D₀ (vcOf S) (qN N) := by
  filter_upwards [hw, hcl, hcalls, hq.eventually_ge_atTop (max 1 S.pcppAlg.minimumArity)] with N hwN hclN hcN hqN
  intro x g hg
  have harity : g.q = qN N := by
    show (S.request x g.oracle).arity = _
    rw [UnionCallCount.request_arity_of, hwN]
    exact max_eq_left (by omega)
  obtain ⟨Λ, hΛ1, hΛ⟩ := hF.mass g.q
  have hm : (g.checkData g.translation).mass = Λ := hΛ
  have hs1 : 1 ≤ (g.checkData g.translation).s := hF.size g.q
  have hDs : (g.checkData g.translation).s = sp (qN N) := by
    show S.gridSize g.q = _
    rw [hgs, harity]
  have hΛs : Λ ≤ sp (qN N) := by
    have := hgm g.q
    rw [hΛ, harity] at this
    exact_mod_cast this
  have hsSB : sp (qN N) ≤ SB Csp (qN N) := sp_le_SB Csp sp hsp _
  have hsg := hg.2.2.1
  have hmne := mass_ne hF g
  have hsne := s_ne hF g
  have hperm : ∀ u, u ∈ myV (g.checkData g.translation) ∨ u ∈ myQ (g.checkData g.translation) ∨
      u ∈ myMu (g.checkData g.translation) →
      u ∈ (g.checkData g.translation).termsV ∨ u ∈ (g.checkData g.translation).termsQ ∨
        u ∈ (g.checkData g.translation).termsMu := by
    intro u hu
    rcases hu with hu | hu | hu
    · exact Or.inl ((termsV_perm _ hmne hsne).mem_iff.2 hu)
    · exact Or.inr (Or.inl ((termsQ_perm _ hmne hsne).mem_iff.2 hu))
    · exact Or.inr (Or.inr ((termsMu_perm _ hmne hsne).mem_iff.2 hu))
  have hentry : ∀ t ∈ (goodOut S hF g hg.2.2.2 0 0 0).table, t.req.1.n = qN N ∧
      t.e.mag ≤ MB Csp (qN N) ∧ t.e.word.length ≤ wc * (qN N + 1) ^ wd := by
    intro t ht
    obtain ⟨k, u, hu, he, hreq⟩ := mem_tableAll _ _ _ _ _ _ _ t ht
    have hu' := hperm u hu
    have hn : t.req.1.n = qN N := by
      rw [hreq, CheckB.terms_n _ u hu']
      exact harity
    refine ⟨hn, ?_, ?_⟩
    · have hmag := CheckB.terms_mag _ Λ hm hs1 hsg u hu'
      rw [he]
      show (scaledZ (g.checkData g.translation).s u.1).natAbs ≤ _
      refine hmag.trans ?_
      unfold MB
      rw [hDs]
      have h1 : Λ + sp (qN N) ≤ SB Csp (qN N) + SB Csp (qN N) := by omega
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h1 4)
    · rw [t.hw]
      have := hword t.req.1 t.req.2
      rwa [hn] at this
  refine ⟨by omega, ?_, fun t ht => (hentry t ht).1, ?_, ?_, ?_, ?_⟩
  · show unionBits g.q = _
    rw [harity]
  · exact foldr_max_le _ _ fun a ha => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
      exact (hentry t ht).2.1
  · exact foldr_max_le _ _ fun a ha => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
      exact (hentry t ht).2.2
  · show (tableAll _ _ _ _ _ _ _).length ≤ _
    rw [FrontOutRef.tableAll_length, ← (termsV_perm _ hmne hsne).length_eq, ← (termsQ_perm _ hmne hsne).length_eq,
      ← (termsMu_perm _ hmne hsne).length_eq]
    have hc := hcN x g hg.1 g.translation
    have hs : (g.checkData g.translation).schedule.length = (g.checkData g.translation).termsV.length +
        (g.checkData g.translation).termsQ.length + (g.checkData g.translation).termsMu.length := by
      simp only [UnionCheckData.schedule, List.length_map, List.length_append]
    have hp : qN N ^ ucd ≤ (qN N + 1) ^ ucd := Nat.pow_le_pow_left (by omega) _
    omega
  · intro i
    have ha := accStart_le S (g.checkData g.translation) (unionBits g.q) Λ hm i
    have hc := hclN x g hg.1 g.translation
    have hp : 2 ^ unionBits g.q ≤ 4 * (qN N + 1) := by rw [harity]; exact two_pow_unionBits _
    show accStart S (g.checkData g.translation) (unionBits g.q) i ≤ _
    refine ha.trans ?_
    unfold AB
    rw [hDs]
    have hΛ' : 1 + Λ ≤ 1 + SB Csp (qN N) := by omega
    gcongr

end Atoms

/-! ## The capacities and the loop's hypotheses at the pinned setup -/

section Good
open NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
variable (l : Literals) (F : Split.GateFree l) (e coef A : ℕ)

/-- The union's ledger at margin `e`. -/
noncomputable abbrev BU : TimeBudget (kE l e) (Split.gate0 l F).E :=
  (Split.gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)

/-- **The front's capacity** `(32·coef + 1)·2^{q−⌊k/4⌋}·(q+1)^{A_main}` (approved). -/
noncomputable def capQ (q : ℕ) : ℕ :=
  (32 * coef + 1) * (2 ^ (q - (BU l F e coef A).kOf q / 4) * (q + 1) ^ (Split.gate0 l F).E.Amain)

/-- **The loop's scratch capacity** `1000·(q+6)·cap`. -/
noncomputable def RQ (q : ℕ) : ℕ := 1000 * (q + 6) * capQ l F e coef A q

theorem capQ_pos (q : ℕ) : 1 ≤ capQ l F e coef A q := by
  unfold capQ
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by positivity) (by positivity)))

/-- The per-call factor of the front's capacity and loop: `2·10⁶·2^{A_main}`. -/
noncomputable def KfC : ℕ := 2000000 * 2 ^ (Split.gate0 l F).E.Amain

theorem callBudget_upper : ∀ᶠ q : ℕ in atTop, (BU l F e coef A).callBudget q ≤
    4 * coef * (2 ^ (q - (BU l F e coef A).kOf q / 4) * (q + 1) ^ (Split.gate0 l F).E.Amain) :=
  FrontLedger.cb_upper (Split.gate0 l F).E coef (Split.gate0 l F).row
    (Ledger.nativeWidthData (kE l e) (Split.gate0 l F).Apad (Split.gate0 l F).E (Split.gate0 l F).hσ A (aE l e)
      (haE l e))

theorem callBudget_lower (q : ℕ) :
    coef * (2 ^ (q - (BU l F e coef A).kOf q / 4) * q ^ (Split.gate0 l F).E.Amain) ≤ (BU l F e coef A).callBudget q :=
  FrontLedger.cb_lower (Split.gate0 l F).E coef (Split.gate0 l F).row
    (Ledger.nativeWidthData (kE l e) (Split.gate0 l F).Apad (Split.gate0 l F).E (Split.gate0 l F).hσ A (aE l e)
      (haE l e)) q

theorem two_pow_small (c d : ℕ) : ∀ᶠ q : ℕ in atTop,
    c * (q + 1) ^ d ≤ 2 ^ (q - (BU l F e coef A).kOf q / 4) :=
  FrontLedger.poly_small (Split.gate0 l F).E coef (Split.gate0 l F).row
    (Ledger.nativeWidthData (kE l e) (Split.gate0 l F).Apad (Split.gate0 l F).E (Split.gate0 l F).hσ A (aE l e)
      (haE l e)) c d

/-- **The capacity is within `34·2^{A_main}` of the per-call budget** (for `q ≥ 1`). -/
theorem capQ_le (hcoef : 1 ≤ coef) (q : ℕ) (hq : 1 ≤ q) :
    capQ l F e coef A q + 1 ≤ 34 * 2 ^ (Split.gate0 l F).E.Amain * (BU l F e coef A).callBudget q := by
  have hlow := callBudget_lower l F e coef A q
  set m := q - (BU l F e coef A).kOf q / 4
  set Am := (Split.gate0 l F).E.Amain
  set cb := (BU l F e coef A).callBudget q
  have hX : (q + 1) ^ Am ≤ 2 ^ Am * q ^ Am := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h1 : 1 ≤ 2 ^ m * q ^ Am := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by positivity))
  have h1' : 1 ≤ coef * (2 ^ m * q ^ Am) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 1 ≤ cb := le_trans h1' hlow
  show (32 * coef + 1) * (2 ^ m * (q + 1) ^ Am) + 1 ≤ 34 * 2 ^ Am * cb
  have h3 : (32 * coef + 1) * (2 ^ m * (q + 1) ^ Am) ≤ (33 * coef) * (2 ^ m * (2 ^ Am * q ^ Am)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hX)
  have h4 : (33 * coef) * (2 ^ m * (2 ^ Am * q ^ Am)) = 33 * 2 ^ Am * (coef * (2 ^ m * q ^ Am)) := by ring
  have h5 : 33 * 2 ^ Am * (coef * (2 ^ m * q ^ Am)) ≤ 33 * 2 ^ Am * cb := Nat.mul_le_mul_left _ hlow
  have h6 : 34 * 2 ^ Am * cb = 33 * 2 ^ Am * cb + 2 ^ Am * cb := by ring
  have h7 : 1 ≤ 2 ^ Am * cb := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  omega

variable (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- **The valid branch meets the loop's hypotheses, fits its accumulators, and stays within the per-call budget**,
past a threshold, at the capacities `capQ`, `RQ`, `RQ + 1`. -/
theorem good_facts (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A)) (hF : GridFacts (SUE l F e coef A L hL)) :
    ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → ∀ (x : BitInput N) (g : UnionGuess (SUE l F e coef A L hL) x)
      (hg : GoodG (SUE l F e coef A L hL) g),
      1 ≤ (BU l F e coef A).q N ∧
      LoopHyps (capQ l F e coef A ((BU l F e coef A).q N)) (RQ l F e coef A ((BU l F e coef A).q N))
          (RQ l F e coef A ((BU l F e coef A).q N) + 1) (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).p
          ((BU l F e coef A).q N) (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).Mm
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).Wm
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).acc0
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).table ∧
      (∀ i, Sched.accOf P (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).p
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).acc0
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).table
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).table.length i ≤
        capQ l F e coef A ((BU l F e coef A).q N)) ∧
      Sched.loopCost (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).Mm
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).Wm
          ((BU l F e coef A).callBudget ((BU l F e coef A).q N))
          (goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0).p (RQ l F e coef A ((BU l F e coef A).q N)) + 2 ≤
        KfC l F * ((BU l F e coef A).q N + 1) ^ (Split.callDegMargin - 1) *
          (BU l F e coef A).callBudget ((BU l F e coef A).q N) := by
  obtain ⟨K₀, D₀, hcl⟩ := S2_clause l (Split.gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL
    (Split.gateRel_gate0 l F).apad
  obtain ⟨wc, wd, -, hwb⟩ := PrimAsm.CallSize.wordBound_poly
  have hword : ∀ r : PrimRequest, (IUE l F e coef A).Call r → r.word.length ≤ wc * (r.n + 1) ^ wd := fun r h =>
    (PrimAsm.CallSize.gate_word_length_le l F (kE l e) coef A (aE l e) (haE l e) r h).trans (hwb r.n)
  have hq : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (Split.gate0 l F).Apad
  have hat := valid_atoms_of (SUE l F e coef A L hL) hF (Split.gate0 l F).row.sp (Split.gate0 l F).row.Csp
    (Split.gate0 l F).row.sp_le (S2_gridSize l (Split.gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL)
    (fun q => by
      rw [show (SUE l F e coef A L hL).gridMass = gridMassOf (gateCδ1 l) (Split.gate0 l F).row.sp from
        S2_gridMass l (Split.gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL]
      exact gridMassOf_le _ _ q)
    (BU l F e coef A).q hq (S2_width l (Split.gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL
      (Split.gateRel_gate0 l F).apad) K₀ D₀ hcl (Split.unionCallDeg l)
    (UnionCallCount.setupF_calls_le l (kE l e) coef A (aE l e) (haE l e) F L hL) wc wd hword
  obtain ⟨c, d, hneed⟩ := needCap_pq (Split.gate0 l F).row.Csp K₀ D₀ (vcOf (SUE l F e coef A L hL)) wc wd
    (Split.unionCallDeg l)
  have hup := hq.eventually (callBudget_upper l F e coef A)
  have hsm := hq.eventually (two_pow_small l F e coef A c d)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hat.and (hup.and hsm))
  refine ⟨N₁, fun N hN x g hg => ?_⟩
  obtain ⟨hatN, hcbU, hpoly⟩ := hN₁ N hN
  obtain ⟨hq1, hp, hn, hMm, hWm, hlen, hacc⟩ := hatN x g hg
  have hcapc := capQ_le l F e coef A hcoef _ hq1
  set q := (BU l F e coef A).q N with hqdef
  set o := goodOut (SUE l F e coef A L hL) hF g hg.2.2.2 0 0 0 with ho
  set cb := (BU l F e coef A).callBudget q with hcb
  set Am := (Split.gate0 l F).E.Amain with hAm
  set m := q - (BU l F e coef A).kOf q / 4 with hm
  set T := 2 ^ m * (q + 1) ^ Am with hT
  set capv := capQ l F e coef A q with hcapv
  have hcapT : capv = (32 * coef + 1) * T := rfl
  have hRv : RQ l F e coef A q = 1000 * (q + 6) * capv := rfl
  have hTge : 2 ^ m ≤ T := Nat.le_mul_of_pos_right _ (by positivity)
  have hnc0 := (hneed q).trans (hpoly.trans hTge)
  have h8 : 8 * cb ≤ 32 * (coef * T) := by
    have e1 : 4 * coef * (2 ^ m * (q + 1) ^ Am) = 4 * (coef * T) := by rw [hT]; ring
    have := hcbU
    rw [e1] at this
    omega
  have hcap2 : capv = 32 * (coef * T) + T := by rw [hcapT]; ring
  have hsplit : 8 * cb + needCap (Split.gate0 l F).row.Csp K₀ D₀ (vcOf (SUE l F e coef A L hL)) wc wd
      (Split.unionCallDeg l) q ≤ capv := by omega
  clear_value capv T m
  have hnc := hsplit
  unfold needCap at hnc
  have h2p : 2 ^ o.p ≤ 4 * (q + 1) := by rw [hp]; exact two_pow_unionBits q
  have hpq : o.p ≤ q + 1 := by rw [hp]; exact unionBits_le q
  have hcapA : ∀ i, o.acc0 i + (o.table.length + 2) * (o.Mm * (8 * 2 ^ o.p)) ≤ capv := by
    intro i
    have hmul : (o.table.length + 2) * (o.Mm * (8 * 2 ^ o.p)) ≤
        ((q + 1) ^ Split.unionCallDeg l + 2) * (MB (Split.gate0 l F).row.Csp q * (8 * (4 * (q + 1)))) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul hMm (Nat.mul_le_mul_left 8 h2p))
    have := hacc i
    omega
  have hstage : Sched.stageCost o.Mm o.Wm cb (2 * cb + 3) o.p + 1 ≤ RQ l F e coef A q := by
    unfold Sched.stageCost Round.roundCost
    have hY : 400 * (2 * cb + 3 + 2) + 100 * 2 ^ o.p + 200 ≤ 101 * capv := by omega
    have hp4 : (o.p + 4) * (400 * (2 * cb + 3 + 2) + 100 * 2 ^ o.p + 200) ≤ (q + 5) * (101 * capv) :=
      Nat.mul_le_mul (by omega) hY
    have hB : o.Mm * (20 * (8 * 2 ^ o.p) + 7 + 4) ≤ MB (Split.gate0 l F).row.Csp q * (160 * (4 * (q + 1)) + 11) :=
      Nat.mul_le_mul hMm (by omega)
    have e1 : (q + 5) * (101 * capv) = 101 * ((q + 5) * capv) := by ring
    have e2 : 1000 * (q + 6) * capv = 1000 * ((q + 5) * capv) + 1000 * capv := by ring
    rw [hRv]
    omega
  have hR1 : capv + 1 ≤ RQ l F e coef A q := by
    rw [hRv]
    have := Nat.mul_le_mul_right capv (show 2 ≤ 1000 * (q + 6) by omega)
    omega
  have hcbeq : ((Split.gate0 l F).budget (kE l e) coef A (aE l e) (haE l e)).callBudget q = cb := rfl
  refine ⟨hq1, ⟨hn, mag_le _, word_le _, ?_, ?_, hcapA, hR1, hstage, le_rfl⟩, ?_, ?_⟩
  · omega
  · omega
  · intro i
    have h1 := Sched.accOf_le P o.p o.acc0 o.table o.Mm (mag_le _) o.table.length i
    have h2 : o.table.length * (o.Mm * (4 * 2 ^ o.p)) ≤ (o.table.length + 2) * (o.Mm * (8 * 2 ^ o.p)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
    have := hcapA i
    omega
  · have hdm : Split.callDegMargin - 1 = 7 := rfl
    rw [hdm]
    unfold Sched.loopCost
    have hRcb : RQ l F e coef A q ≤ 6000 * (q + 1) * (34 * 2 ^ Am * cb) := by
      rw [hRv]
      calc 1000 * (q + 6) * capv ≤ 1000 * (6 * (q + 1)) * (34 * 2 ^ Am * cb) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
        _ = 6000 * (q + 1) * (34 * 2 ^ Am * cb) := by ring
    have hq7 : q + 1 ≤ (q + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
    have hfin : 5 * (6000 * (q + 1) * (34 * 2 ^ Am * cb)) ≤ KfC l F * (q + 1) ^ 7 * cb := by
      unfold KfC
      calc 5 * (6000 * (q + 1) * (34 * 2 ^ Am * cb)) = 1020000 * 2 ^ Am * ((q + 1) * cb) := by ring
        _ ≤ 2000000 * 2 ^ Am * ((q + 1) ^ 7 * cb) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) (Nat.mul_le_mul_right _ hq7)
        _ = 2000000 * 2 ^ Am * (q + 1) ^ 7 * cb := by ring
    omega

end Good

/-! ## The front's reference output meets F2 -/

section Fields
open NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
variable (l : Literals) (F : Split.GateFree l) (e coef A : ℕ) (L : Language)
  (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- **The pinned setup's grid facts**: the mass `Λ̄(q) = ⌈2/ε_t⌉ ≥ 1` is a natural number, the grid is nonempty. -/
theorem gridFacts_SUE : GridFacts (SUE l F e coef A L hL) where
  mass q := ⟨rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q, one_le_lambda (gateZeta_pos l) (gateZeta_lt l) q, by
    rw [S2_gridMass l (Split.gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL]
    exact gridMassOf_rowB (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCδ1_pos l) q⟩
  size q := by
    rw [S2_gridSize l (Split.gate0 l F) (kE l e) coef A (aE l e) (haE l e) L hL]
    exact one_le_gridSize (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCδ1_pos l) q

/-- **F2 at the approved capacities**: past a threshold `N₁`, for every onset `≥ N₁`, the front's reference output
with capacities `capQ`, `RQ`, `RQ + 1` meets `FrontAtW3`'s `loop`, `accFit`, `perCall` and `capAcc` at `K_f = KfC`. -/
theorem outRef_fields (hcoef : 1 ≤ coef) (P : FusedPrimitive (IUE l F e coef A))
    (hF : GridFacts (SUE l F e coef A L hL)) :
    ∃ N₁ : ℕ, ∀ onset, N₁ ≤ onset →
      (∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 →
        (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
          N x w).table ≠ [] →
        LoopHyps (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).cap
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).R
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).Lg
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).p ((BU l F e coef A).q N)
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).Mm
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).Wm
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).acc0
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).table) ∧
      (∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → ∀ i,
        ((outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).keptEnd P).acc i ≤
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).cap) ∧
      (∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → onset ≤ N →
        (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
          N x w).table ≠ [] →
        Sched.loopCost (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).Mm
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).Wm
          ((BU l F e coef A).callBudget ((BU l F e coef A).q N))
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).p
          (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
            (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
            N x w).R + 2 ≤
        KfC l F * ((BU l F e coef A).q N + 1) ^ (Split.callDegMargin - 1) *
          (BU l F e coef A).callBudget ((BU l F e coef A).q N)) ∧
      (∀ N (x : BitInput N) (w : List Bool), w.length = N / 16 → onset ≤ N →
        (outRef (SUE l F e coef A L hL) hF onset (fun N => capQ l F e coef A ((BU l F e coef A).q N))
          (fun N => RQ l F e coef A ((BU l F e coef A).q N)) (fun N => RQ l F e coef A ((BU l F e coef A).q N) + 1)
          N x w).cap + 1 ≤
        KfC l F * ((BU l F e coef A).q N + 1) ^ (Split.callDegMargin - 1) *
          (BU l F e coef A).callBudget ((BU l F e coef A).q N)) := by
  obtain ⟨N₁, hN₁⟩ := good_facts l F e coef A L hL hcoef P hF
  have hq : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (Split.gate0 l F).Apad
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hq.eventually_ge_atTop 1)
  have hcb1 : ∀ N, N₂ ≤ N → 1 ≤ (BU l F e coef A).callBudget ((BU l F e coef A).q N) := fun N hN => by
    have hlow := callBudget_lower l F e coef A ((BU l F e coef A).q N)
    have h1 := hN₂ N hN
    have : 1 ≤ coef * (2 ^ ((BU l F e coef A).q N - (BU l F e coef A).kOf ((BU l F e coef A).q N) / 4) *
        (BU l F e coef A).q N ^ (Split.gate0 l F).E.Amain) :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by positivity) (by positivity)))
    omega
  have hK : ∀ N, N₂ ≤ N → 34 * 2 ^ (Split.gate0 l F).E.Amain * (BU l F e coef A).callBudget ((BU l F e coef A).q N) ≤
      KfC l F * ((BU l F e coef A).q N + 1) ^ (Split.callDegMargin - 1) *
        (BU l F e coef A).callBudget ((BU l F e coef A).q N) := fun N hN => by
    have h1 : 1 ≤ ((BU l F e coef A).q N + 1) ^ (Split.callDegMargin - 1) := Nat.one_le_pow _ _ (by omega)
    unfold KfC
    calc 34 * 2 ^ (Split.gate0 l F).E.Amain * (BU l F e coef A).callBudget ((BU l F e coef A).q N)
        ≤ 2000000 * 2 ^ (Split.gate0 l F).E.Amain * 1 * (BU l F e coef A).callBudget ((BU l F e coef A).q N) :=
          Nat.mul_le_mul_right _ (by rw [mul_one]; exact Nat.mul_le_mul_right _ (by norm_num))
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  refine ⟨max N₁ N₂, fun onset hon => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro N x w _ hne
    unfold outRef at hne ⊢
    split_ifs at hne ⊢ with h
    · exact (hN₁ N (by omega) x _ (Classical.choose_spec h.2).2).2.1
    · exact absurd rfl hne
  · intro N x w _ i
    unfold outRef
    split_ifs with h
    · exact (hN₁ N (by omega) x _ (Classical.choose_spec h.2).2).2.2.1 i
    · show (FrontGate.rejOut.keptEnd P).acc i ≤ 1
      have e : (FrontGate.rejOut (I := IUE l F e coef A)).keptEnd P = FrontGate.rejKept := by
        have := FrontGate.rejOut_kept P
        simpa [FrontOut.kept, FrontOut.keptEnd, FrontGate.rejOut] using this
      rw [e]
      fin_cases i <;> simp [FrontGate.rejKept, FrontGate.rejAcc]
  · intro N x w _ hN hne
    unfold outRef at hne ⊢
    split_ifs at hne ⊢ with h
    · exact (hN₁ N (by omega) x _ (Classical.choose_spec h.2).2).2.2.2
    · exact absurd rfl hne
  · intro N x w _ hN
    unfold outRef
    split_ifs with h
    · have hq1 := (hN₁ N (by omega) x _ (Classical.choose_spec h.2).2).1
      exact (capQ_le l F e coef A hcoef _ hq1).trans (hK N (by omega))
    · show 1 + 1 ≤ _
      have h1 := hcb1 N (by omega)
      have h2 := hK N (by omega)
      have h3 : 34 * 1 * 1 ≤ 34 * 2 ^ (Split.gate0 l F).E.Amain * (BU l F e coef A).callBudget ((BU l F e coef A).q N) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 34 Nat.one_le_two_pow) h1
      omega

end Fields

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps
