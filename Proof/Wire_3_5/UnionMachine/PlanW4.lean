import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.Assembly.Ok
import Proof.Wire_3_5.UnionMachine.SetupFactsE
import Proof.Wire_3_5.UnionMachine.Decision
import Proof.Wire_3_5.UnionMachine.UnionCallCount

/-! # C6: leaf U with the atom test's completeness

"It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid" (P3:3669-3671); the
completeness the atom test leaves is for accepting guesses whose atoms pass it (P3:3711-3716). PlanW3's worker
(`workerMeaning2`, the front at `FrontsFWE3`) meets `CompleteForEventuallyOk` directly: the padded
encoding of an accepting guess `g` with `AtomsOkG g` is accepted (`completeOk`, PlanW3's argument with `g` itself).
* **`completeOk`**; `leafAtPosE4` (`Split.UnionLeafAt2`), the coefficient-`0` branch `(PlanW2.leafAtZeroE …).toOk`;
  `unionLeafF_of_workersE4`, `unionLeafF_planE4`, `union_planW4G`;
* **`union_planW4 c1 fronts : ∀ l, Split.UnionLeafF2 l`** (U7 `decideF`, the call count and the margin-generic
  setup residuals filled; residuals `c1 : C1Impl` unchanged, `fronts` at `FrontsFWE3`).

Paper quantity of the main type: `UnionLeafF2 l`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PlanW4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.UnionMachine.PlanW3

section Worker
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}
  {P : FusedPrimitive I}

/-- **Completeness with the atom test**: past the worker's onset, an accepting guess whose atoms pass the test,
padded to the `⌊N/16⌋`-bit witness, is accepted. -/
theorem completeOk (W : WorkerAt3 S P) : CompleteForEventuallyOk S P W.machine := by
  refine ⟨W.onset, fun N hN z g hg hat => ?_⟩
  have hlen : g.word.length ≤ N / 16 := hg.2.2.1
  set w := encodeGuess g ++ List.replicate (N / 16 - g.word.length) false with hw
  have hwl : w.length = N / 16 := by
    simp only [hw, List.length_append, List.length_replicate, encodeGuess]
    omega
  have hdec : decodeGuess S z w = some g := decodeGuess_encodeGuess g _
  have hrun : unionSlackRun S z UnionGuess.translation W.callOk P unionBits w = true := by
    unfold unionSlackRun
    rw [hdec]
    exact unionSlackCheck_of_accepts P unionBits g W.callOk (W.hok N hN z g) hg
  have hok : PlanW3.atomsOk S z w := by
    intro g'' h
    rw [hdec] at h
    cases h
    exact hat
  have hw' : List.ofFn (fun i : Fin (N / 16) => w.get ⟨i.val, by omega⟩) = w := by
    apply List.ext_get
    · simp [hwl]
    · intro n h1 h2; simp
  refine (weakOf_accepts W.p W.ht W.result W.fuel _ W.run N z).2 ⟨fun i => w.get ⟨i.val, by omega⟩, hN, ?_, ?_⟩
  · rw [hw']; exact hok
  · rw [hw']; exact hrun

end Worker

section Leaf
variable (l : Literals)

/-- The positive-coefficient branch with the atom test's completeness. -/
noncomputable def leafAtPosE4 (e : ℕ) (F : GateFree l) (coef A : ℕ) (facts : SetupFactsFE l e)
    (W : ∀ (P : FusedPrimitive (IUE l F e coef A)) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L),
      WorkerAt3 (SUE l F e coef A L hL) P) (hA : 3 ≤ A) :
    UnionLeafAt2 (IUE l F e coef A) (fun L hL => SUE l F e coef A L hL) := by
  classical
  exact
  { build := fun P L => if hL : InNTIME (fun n => n ^ (kE l e + 2)) L then (W P L hL).machine else rejectAll
    soundness := fun P L hL => by
      rw [dif_pos hL]
      exact (W P L hL).oneSided (facts F coef A L hL)
    time := fun P L N hN => by
      by_cases hL : InNTIME (fun n => n ^ (kE l e + 2)) L
      · rw [dif_pos hL]
        exact (W P L hL).split N hN
      · rw [dif_neg hL, rejectAll_runtime]
        have h1 : 1 ≤ (N + 1) ^ aE l e := Nat.one_le_pow _ _ (Nat.succ_pos N)
        have : 3 ≤ A * (N + 1) ^ aE l e := le_trans hA (Nat.le_mul_of_pos_right _ h1)
        exact le_trans this (Nat.le_add_right _ _)
    complete := fun P L hL => by
      show CompleteForEventuallyOk _ P (if hL : InNTIME (fun n => n ^ (kE l e + 2)) L then (W P L hL).machine
        else rejectAll)
      rw [dif_pos hL]
      exact completeOk (W P L hL) }

/-- **Layer A: leaf U with the atom test from workers.** -/
noncomputable def unionLeafF_of_workersE4 (e : ℕ) (facts : SetupFactsFE l e) (acc : AcceptsCallFE l e)
    (W : ∀ F : GateFree l, GateFreeOK l F → WorkersFE3 l e F) : UnionLeafF2 l :=
  fun F hF =>
  ⟨kE l e, (W F hF).1, aE l e, haE l e, fun coef =>
    if hc : 1 ≤ coef then leafAtPosE4 l e F coef (W F hF).1 facts ((W F hF).2.2 coef hc) (W F hF).2.1
    else (leafAtZeroE l e F coef (W F hF).1 (W F hF).2.1 hc acc).toOk⟩

/-- **Leaf U with the atom test at one literal set** (the plan). -/
noncomputable def unionLeafF_planE4 (c1 : C1Impl) (dec : DecideF) (e : ℕ)
    (fronts : ∀ F : GateFree l, GateFreeOK l F → FrontsFWE3 e l F) (count : CallCountF l) (acc : AcceptsCallFE l e)
    (facts : SetupFactsFE l e) : UnionLeafF2 l :=
  unionLeafF_of_workersE4 l e facts acc (workers_of_stagesE3 l c1 dec e fronts count)

end Leaf

/-- **Leaf U's enclosing application with the atom test**, every helper type an explicit residual. -/
noncomputable def union_planW4G (c1 : C1Impl) (dec : DecideF)
    (fronts : ∀ l : Literals, Σ e : ℕ, ∀ F : GateFree l, GateFreeOK l F → FrontsFWE3 e l F)
    (count : ∀ l : Literals, CallCountF l) (acc : ∀ (l : Literals) (e : ℕ), AcceptsCallFE l e)
    (facts : ∀ (l : Literals) (e : ℕ), SetupFactsFE l e) : ∀ l : Literals, UnionLeafF2 l :=
  fun l => unionLeafF_planE4 l c1 dec (fronts l).1 (fronts l).2 (count l) (acc l (fronts l).1) (facts l (fronts l).1)

/-- **Leaf U with the atom test from C1 and the fronts** (U7, the call count and the setup residuals filled). -/
noncomputable def union_planW4 (c1 : C1Impl)
    (fronts : ∀ l : Literals, Σ e : ℕ, ∀ F : GateFree l, GateFreeOK l F → FrontsFWE3 e l F) :
    ∀ l : Literals, UnionLeafF2 l :=
  union_planW4G c1 Decision.decideF fronts
    (fun l kclk coef A a ha F L hL => Transfer.UnionCallCount.setupF_calls_le l kclk coef A a ha F L hL)
    SetupFactsE.acceptsCallFE SetupFactsE.setupFactsFE

end NearCubicWires.WireExponent3_5.UnionMachine.PlanW4
