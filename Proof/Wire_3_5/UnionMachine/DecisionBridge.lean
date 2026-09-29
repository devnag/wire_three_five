import Proof.Wire_3_5.UnionMachine.Bridge
import Proof.Wire_3_5.UnionMachine.Decision

/-! # C6, U5 bridge: the decision after the loop is the slack check (P3:3484-3491)

Realizes, for the call table the front builds, the equality between the machine's decision and `tr:thresholds` with
the slack of: "accept only if `V̂ ≤ 2v₀`, `Q̂ ≤ 1 + v₀` and `μ̂ ≥ τ`" (P3:3485-3489), evaluated at the rounded
answers `⌊v·2^p⌋/2^p` with the thresholds relaxed by `δ`.

* `threshAcc T_V T_Q T_μ`: the accumulators' start, each test's pair `(T⁻, T⁺)`, whose difference is `−T`;
* **`decision_accOf`**: after the loop, `decisionOf` is `Σ_V ≤ T_V ∧ Σ_Q ≤ T_Q ∧ T_μ ≤ Σ_μ` over the entries' signed
  terms (M3 `accOf_diff`);
* `tableAll`: the call table of the three term lists (`V`, then `Q`, then `μ`), each entry the sign and magnitude of
  `c·s⁴` and the request word (`Bridge.tableOfTerms`);
* **`decision_slack`**: on that table, with the thresholds `⌊s⁴2^p·2M(2v₀+δ)⌋`, `⌊s⁴2^p·2M(1+v₀+δ)⌋`,
  `⌈s⁴2^p·M(τ−δ)⌉`, the decision after the loop IS `slackCheck` at the rounded answers, when the grid signs are valid
  and every scheduled call passed `callOk` (`Bridge.slackCheck_int`, `Bridge.table_sum`).

Paper quantity of the main statement: the machine's decision `decisionOf` against `slackCheck` (= `tr:thresholds`
with slack) at the answers `roundQ p ∘ P.value`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge

/-- **The accumulators' start**: each test's pair `(T⁻, T⁺)` (difference `−T`): `V`, `Q` against upper thresholds,
`μ` against a lower one. -/
def threshAcc (TV TQ TM : ℤ) : Fin 6 → ℕ :=
  ![(-TV).toNat, TV.toNat, (-TQ).toNat, TQ.toNat, (-TM).toNat, TM.toNat]

theorem neg_toNat_sub (x : ℤ) : ((-x).toNat : ℤ) - (x.toNat : ℤ) = -x := by
  have := Int.toNat_sub_toNat_neg x
  omega

section Loop
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- **The decision after the loop** compares each test's sum of signed terms with its threshold. -/
theorem decision_accOf (p : ℕ) (TV TQ TM : ℤ) (Ls : List (Sched.TEntry I)) :
    decisionOf (Sched.accOf P p (threshAcc TV TQ TM) Ls Ls.length) =
      (decide ((Ls.map (Sched.signedTerm P p 0)).sum ≤ TV) &&
        decide ((Ls.map (Sched.signedTerm P p 1)).sum ≤ TQ) &&
          decide (TM ≤ (Ls.map (Sched.signedTerm P p 2)).sum)) := by
  set a := Sched.accOf P p (threshAcc TV TQ TM) Ls Ls.length with ha
  have h0 : ((a 0 : ℕ) : ℤ) - (a 1 : ℕ) =
      (((threshAcc TV TQ TM 0 : ℕ) : ℤ) - (threshAcc TV TQ TM 1 : ℕ)) + (Ls.map (Sched.signedTerm P p 0)).sum :=
    Sched.accOf_diff P p (threshAcc TV TQ TM) Ls 0
  have h1 : ((a 2 : ℕ) : ℤ) - (a 3 : ℕ) =
      (((threshAcc TV TQ TM 2 : ℕ) : ℤ) - (threshAcc TV TQ TM 3 : ℕ)) + (Ls.map (Sched.signedTerm P p 1)).sum :=
    Sched.accOf_diff P p (threshAcc TV TQ TM) Ls 1
  have h2 : ((a 4 : ℕ) : ℤ) - (a 5 : ℕ) =
      (((threshAcc TV TQ TM 4 : ℕ) : ℤ) - (threshAcc TV TQ TM 5 : ℕ)) + (Ls.map (Sched.signedTerm P p 2)).sum :=
    Sched.accOf_diff P p (threshAcc TV TQ TM) Ls 2
  have e0 : (((threshAcc TV TQ TM 0 : ℕ) : ℤ) - (threshAcc TV TQ TM 1 : ℕ)) = -TV := neg_toNat_sub TV
  have e1 : (((threshAcc TV TQ TM 2 : ℕ) : ℤ) - (threshAcc TV TQ TM 3 : ℕ)) = -TQ := neg_toNat_sub TQ
  have e2 : (((threshAcc TV TQ TM 4 : ℕ) : ℤ) - (threshAcc TV TQ TM 5 : ℕ)) = -TM := neg_toNat_sub TM
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  unfold decisionOf
  congr 1
  · congr 1
    · exact decide_eq_decide.mpr (by omega)
    · exact decide_eq_decide.mpr (by omega)
  · exact decide_eq_decide.mpr (by omega)

/-- **The call table** of the three tests' term lists: `V`, then `Q`, then `μ`. -/
def tableAll (s : ℕ) (TV TQ TM : List (ℚ × PrimRequest)) (hV : ∀ t ∈ TV, I.Call t.2)
    (hQ : ∀ t ∈ TQ, I.Call t.2) (hM : ∀ t ∈ TM, I.Call t.2) : List (Sched.TEntry I) :=
  tableOfTerms 0 s TV hV ++ tableOfTerms 1 s TQ hQ ++ tableOfTerms 2 s TM hM

theorem tableAll_sum (s p : ℕ) (TV TQ TM : List (ℚ × PrimRequest)) (hV : ∀ t ∈ TV, I.Call t.2)
    (hQ : ∀ t ∈ TQ, I.Call t.2) (hM : ∀ t ∈ TM, I.Call t.2) (k : Fin 3) :
    ((tableAll s TV TQ TM hV hQ hM).map (Sched.signedTerm P p k)).sum =
      (if (0 : Fin 3) = k then zSum s TV (fun r => ⌊P.value r * 2 ^ p⌋) else 0) +
        (if (1 : Fin 3) = k then zSum s TQ (fun r => ⌊P.value r * 2 ^ p⌋) else 0) +
          (if (2 : Fin 3) = k then zSum s TM (fun r => ⌊P.value r * 2 ^ p⌋) else 0) := by
  unfold tableAll
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, table_sum, table_sum, table_sum]

/-- **The decision is the slack check** (P3:3485-3491): on the table of the check data's three term lists, from
the thresholds preloaded into the accumulators, the decision after the loop is `slackCheck` at the rounded answers,
whenever the grid signs are valid and every scheduled call passed `callOk`. -/
theorem decision_slack (D : UnionCheckData) (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (p : ℕ) (v0 τ δ : ℚ)
    (callOk : PrimRequest → Bool) (hV : ∀ t ∈ D.termsV, I.Call t.2) (hQ : ∀ t ∈ D.termsQ, I.Call t.2)
    (hM : ∀ t ∈ D.termsMu, I.Call t.2) (hsg : D.signsOk = true) (hall : D.schedule.all callOk = true) :
    decisionOf (Sched.accOf P p (threshAcc ⌊scaleVQ D p * (2 * v0 + δ)⌋ ⌊scaleVQ D p * (1 + v0 + δ)⌋
        ⌈scaleMu D p * (τ - δ)⌉) (tableAll D.s D.termsV D.termsQ D.termsMu hV hQ hM)
        (tableAll D.s D.termsV D.termsQ D.termsMu hV hQ hM).length) =
      slackCheck D (fun r => roundQ p (P.value r)) v0 τ δ callOk := by
  rw [decision_accOf, tableAll_sum, tableAll_sum, tableAll_sum]
  have e := slackCheck_int D Λ hm hs p (fun r => ⌊P.value r * 2 ^ p⌋) v0 τ δ callOk
  have hr : (fun r => roundQ p (P.value r)) = (fun r => ((⌊P.value r * 2 ^ p⌋ : ℤ) : ℚ) / 2 ^ p) := rfl
  rw [hr, e, hsg, hall]
  simp

end Loop


end NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
