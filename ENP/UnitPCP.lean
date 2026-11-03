import Proof.PCP.ProjectionCompaction
import Proof.Amplification.RecoveryCanonicalChoice
import Outer.Circuit

/-!
# Stages 1 and 3 (semantic part): listed input/output pairs as a raw projection PCP

The near-cubic-gates paper's uniform recovery (sec:all-lengths, the E^NP paragraph): "First, a formula over the description of `B_src` with the `N`
constraints (eq:source-check) … finds the first source circuit `B*_src`, or shows that there is none … Third, a formula
over the description of `B_pf` with the `2^{ℓ_out}` constraints `B_pf(a0^{q−ℓ_out}) = O*(a)` … finds the first `B*_pf`, or
shows that there is none." the extraction of the hard table: "Descriptions are ordered lexicographically, and 'first' refers to this order."

Both formulas are "a bounded circuit on `q` inputs agreeing with a listed table on the points `(bin_w(i), 0^{q−w})`".
Proof 1's bounded-oracle formula (`boundedOracleVerifierCircuit`, executed by the source-free
`RecoveryBoundedColdGraph.machine`) is stated for an arbitrary RAW projection PCP. A raw PCP has one fixed 3CNF decision,
so the listed values ride on the decision: `unitPCP w vals` has `vals.length` queries, query `i` at the CONSTANT address
`bin_w(i)`, and the decision is the conjunction of the unit clauses `y_i = vals[i]`. After the standard normalization to
width `R` (zero-suffix face) and compaction, every row says `B(bin_w(i)0^{R−w}) = vals[i]` for all `i`
(`unitOuter_accepts`). Stage 1 is `vals = z` with `w = ν` (`unitOuter_check`), stage 3 is `vals = tt(O*)` with `w = ℓ`
(`unitOuter_match`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionPCPPadding NearCubicWires.ExecutableInterfaces

/-- The unit clause `y_i = v`, as a three-literal clause with three equal literals (the near-cubic-gates paper's uniform recovery, the listed
constraints of stages 1 and 3). -/
def unitClause {Q : ℕ} (i : Fin Q) (v : Bool) : Fin 3 → Literal Q :=
  fun _ => if v then .positive i else .negative i

/-- A lifted unit clause literal reads `y_i = v` (the near-cubic-gates paper's uniform recovery, the listed constraints). -/
theorem lift_unit_eval {Q : ℕ} (i : Fin Q) (v : Bool) (k : Fin 3) (a : BitInput Q) :
    (liftQueryLiteral (le_refl Q) (unitClause i v k)).eval a = (a i == v) := by
  cases v <;> cases h : a i <;> simp [unitClause, liftQueryLiteral, Literal.eval, h]

/-- The listed-pairs PCP (the near-cubic-gates paper's uniform recovery, stages 1 and 3): width `w`, query `i` at the constant address `bin_w(i)`, and
the decision `⋀_i y_i = vals[i]`. -/
def unitPCP (w : ℕ) (vals : List Bool) : RawProjectionPCP where
  width := w
  queries := vals.length
  queryBits := fun i j => .constant (i.val.testBit j.val)
  decision := ⟨List.ofFn fun i : Fin vals.length => unitClause i (vals.get i)⟩

/-- The normalized and compacted listed-pairs PCP on oracle width `R` (the near-cubic-gates paper's uniform recovery): exactly the PCP that proof 1's
cold graph machine `RecoveryBoundedColdGraph.machine` compiles from the raw `unitPCP w vals` at `Q = vals.length`. -/
def unitOuter (w R : ℕ) (vals : List Bool) (hw : w ≤ R) :=
  compactProjectionPCP ((unitPCP w vals).normalized R vals.length hw le_rfl)

/-- The projected address of query `i` is the point `(bin_w(i), 0^{R−w})` (`Outer.pointOf`). -/
theorem unitOuter_projected (w R : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n)
    (r : BitInput R) (i : Fin vals.length) :
    projectedInput (unitOuter w R vals hw) x r i = Outer.pointOf w R i.val := by
  funext j
  simp only [projectedInput, unitOuter, compactProjectionPCP, RawProjectionPCP.normalized, padProjectionPCP,
    RawProjectionPCP.constant, RawProjectionPCP.raiseQueries, unitPCP, Outer.pointOf]
  by_cases hj : j.val < w
  · simp only [hj, dite_true, i.isLt, liftProjectedRandomBit, ProjectedRandomBit.eval, if_true]
  · simp only [hj, dite_false, ProjectedRandomBit.eval, if_false]

/-- **Bridge (the near-cubic-gates paper's uniform recovery, stages 1 and 3).** On every row, the substituted circuit `B` is accepted by the listed-pairs
PCP exactly when `B(bin_w(i)0^{R−w}) = vals[i]` for every listed `i`. -/
theorem unitOuter_accepts (w R : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n)
    (B : BooleanCircuit R) (r : BitInput R) :
    acceptsOracleCircuit (unitOuter w R vals hw) x B r = true ↔
      ∀ i : Fin vals.length, B.eval (Outer.pointOf w R i.val) = vals.get i := by
  have hp := unitOuter_projected w R vals hw x r
  show (compactThreeCNF (⟨(List.ofFn fun i : Fin vals.length => unitClause i (vals.get i)).map
      (fun c j => liftQueryLiteral (le_refl vals.length) (c j))⟩ : ThreeCNF vals.length)).eval
      (fun query : Fin vals.length => B.eval (projectedInput (unitOuter w R vals hw) x r query)) = true ↔ _
  rw [compactThreeCNF_eval]
  simp only [hp]
  simp only [ThreeCNF.eval]
  rw [List.all_eq_true]
  constructor
  · intro h i
    have hi := h _ (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
    rw [decide_eq_true_eq] at hi
    obtain ⟨k, hk⟩ := hi
    rw [lift_unit_eval, beq_iff_eq] at hk
    exact hk
  · intro h c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc0
    rw [decide_eq_true_eq]
    refine ⟨0, ?_⟩
    rw [lift_unit_eval, beq_iff_eq]
    exact h i

/-- Stage 1 (the near-cubic-gates paper's uniform recovery with eq:source-check): with `vals = z` and `w = ν`, acceptance is `Outer.Check ν z B`, i.e.
`tt_N(B) = z`. -/
theorem unitOuter_check (ν q : ℕ) (hν : ν ≤ q) (z : BitInput (2 ^ ν)) {n : ℕ} (x : BitInput n)
    (B : BooleanCircuit q) (r : BitInput q) :
    acceptsOracleCircuit (unitOuter ν q (List.ofFn z) hν) x B r = true ↔ Outer.Check ν z B := by
  rw [unitOuter_accepts, Outer.Check]
  constructor
  · intro h
    funext i
    have hi := h ⟨i.val, by simp⟩
    simpa [Outer.ttN] using hi
  · intro h i
    have hi := congrFun h ⟨i.val, by simpa using i.isLt⟩
    simpa [Outer.ttN] using hi

/-- Bits of a numeric address, low bit first (the `boolFunctionTable` order). -/
theorem padQuery_bits (ℓ q code : ℕ) :
    Outer.padQuery (q := q) (fun j : Fin ℓ => code.testBit j.val) = Outer.pointOf ℓ q code := by
  funext j
  simp only [Outer.padQuery, Outer.pointOf]
  split <;> simp_all

/-- Stage 3 (the near-cubic-gates paper's uniform recovery: "the `2^{ℓ_out}` constraints `B_pf(a0^{q−ℓ_out}) = O*(a)`"): with `vals` the truth table of
`O*` in address order (`boolFunctionTable`) and `w = ℓ`, acceptance is `O_{B_pf} = O*` with F4's answer `padQuery`. -/
theorem unitOuter_match (ℓ q : ℕ) (hℓ : ℓ ≤ q) (O : BitInput ℓ → Bool) {n : ℕ} (x : BitInput n)
    (B : BooleanCircuit q) (r : BitInput q) :
    acceptsOracleCircuit (unitOuter ℓ q (boolFunctionTable O) hℓ) x B r = true ↔
      ∀ a : BitInput ℓ, B.eval (Outer.padQuery a) = O a := by
  rw [unitOuter_accepts]
  constructor
  · intro h a
    have hlt : encodeBitInput a < 2 ^ ℓ := by
      rw [encodeBitInput_eq_ofBits]
      exact Nat.ofBits_lt_two_pow a
    have hbits : (fun j : Fin ℓ => (encodeBitInput a).testBit j.val) = a := by
      funext j
      rw [encodeBitInput_eq_ofBits]
      exact Nat.testBit_ofBits_lt a j.val j.isLt
    have hi := h ⟨encodeBitInput a, by simpa [boolFunctionTable] using hlt⟩
    rw [← padQuery_bits] at hi
    simp only [boolFunctionTable, List.get_eq_getElem, List.getElem_map, List.getElem_range] at hi
    rw [hbits] at hi
    exact hi
  · intro h i
    have hi := h (fun j : Fin ℓ => i.val.testBit j.val)
    rw [padQuery_bits] at hi
    simpa [boolFunctionTable] using hi


end NearCubicGates.Close.ENP
