import Proof.Wire_3_5.UnionMachine.PlanW2Base
import Proof.Wire_3_5.UnionMachine.FrontGate
import Proof.Wire_3_5.UnionMachine.FrontTableRef

/-! # C6 front, F2: the front's reference output (P3:3669-3691)

What the front leaves for the schedule loop at one input `x` and witness `w` (`FrontAtW3.out`): past the onset, when
the witness decodes to a guess `g` that passes the front's checks (**`GoodG`**: the oracle within `q^G`, every atom in
the description envelope, the grid signs in `{−1,0,1}`, every scheduled call admissible), the call table the table
writer prints (`tableAll` over its term orders `myV`, `myQ`, `myMu`), the slack thresholds in the accumulators, the
rounding precision `unionBits q` and the loop's capacities; otherwise the rejecting output (`FrontGate.rejOut`).
* **`outRef`**, `goodOut`, `callOkI` (`callOk r := [I.Call r]`);
* **`outRef_sem`**: the decision after the loop is the worker's meaning `workerMeaning2`;
* `outRef_len`, `outRef_rej`, `outRef_capPos`.

Paper quantity of the main type: the union machine's decision on a witness (P3:3485-3489, 3669-3691). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge (scaleVQ scaleMu)

section Out
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

open Classical in
/-- **The union's admissibility test** (/M16): `callOk r := [I.Call r]`. -/
noncomputable def callOkI : PrimRequest → Bool := fun r => decide (I.Call r)

theorem callOkI_iff (r : PrimRequest) : callOkI (I := I) r = true ↔ I.Call r := by
  unfold callOkI; simp


variable {S}

theorem calls_of_all (D : UnionCheckData) (h : D.schedule.all (callOkI (I := I)) = true) :
    (∀ t ∈ D.termsV, I.Call t.2) ∧ (∀ t ∈ D.termsQ, I.Call t.2) ∧ (∀ t ∈ D.termsMu, I.Call t.2) := by
  have key : ∀ r ∈ D.schedule, I.Call r := fun r hr => (callOkI_iff r).1 (List.all_eq_true.1 h r hr)
  refine ⟨fun t ht => key _ ?_, fun t ht => key _ ?_, fun t ht => key _ ?_⟩ <;>
    exact List.mem_map_of_mem (f := Prod.snd) (by simp [ht])

/-- The largest magnitude of a table. -/
def maxMag (T : List (Sched.TEntry I)) : ℕ := (T.map fun t => t.e.mag).foldr max 0

/-- The longest request word of a table. -/
def maxW (T : List (Sched.TEntry I)) : ℕ := (T.map fun t => t.e.word.length).foldr max 0

theorem le_foldr_max (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem mag_le (T : List (Sched.TEntry I)) : ∀ t ∈ T, t.e.mag ≤ maxMag T := fun _ ht =>
  le_foldr_max _ _ (List.mem_map_of_mem ht)

theorem word_le (T : List (Sched.TEntry I)) : ∀ t ∈ T, t.e.word.length ≤ maxW T := fun _ ht =>
  le_foldr_max _ _ (List.mem_map_of_mem ht)

end Out

/-! ## The decision -/

section Sem
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)
 

/-! ## The table's length, the rejecting branch, the capacity -/

theorem tableAll_length (s : ℕ) (TV TQ TM : List (ℚ × PrimRequest)) (hV : ∀ t ∈ TV, I.Call t.2)
    (hQ : ∀ t ∈ TQ, I.Call t.2) (hM : ∀ t ∈ TM, I.Call t.2) :
    (tableAll s TV TQ TM hV hQ hM).length = TV.length + TQ.length + TM.length := by
  simp [tableAll, Bridge.tableOfTerms]
  omega

end Sem

end NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef
