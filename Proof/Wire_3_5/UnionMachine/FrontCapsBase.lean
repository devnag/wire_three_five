import Proof.Wire_3_5.UnionMachine.FrontOutRefBase
import Proof.Wire_3_5.UnionMachine.FrontLedger
import Proof.Wire_3_5.UnionMachine.UnionCallCountBase
import Proof.Wire_3_5.Primitive.Writers.CallSizeBase
import Proof.Wire_3_5.Recovery.RecoveryLedger

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
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
 (hL : InNTIME (fun n => n ^ (kclk + 2)) L)

theorem gridMassOf_le (Cδ : ℕ) (sp : ℕ → ℕ) (q : ℕ) : gridMassOf Cδ sp q ≤ (sp q : ℚ) := by
  unfold gridMassOf
  have h1 : Nat.sqrt (sp q / Cδ) ≤ sp q := (Nat.sqrt_le_self _).trans (Nat.div_le_self _ _)
  exact_mod_cast h1

end Setup

/-! ## The clause count -/

section Clause

end Clause

section ClauseS2

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

end Atoms

/-! ## The capacities and the loop's hypotheses at the pinned setup -/

section Good
open NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef NearCubicWires.WireExponent3_5.UnionMachine.PlanW2

end Good

/-! ## The front's reference output meets F2 -/

section Fields
open NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef NearCubicWires.WireExponent3_5.UnionMachine.PlanW2

end Fields

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps
