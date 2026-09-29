import Proof.Wire_3_5.UnionMachine.PlanW3
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
/-- **The union's admissibility test**: `callOk r := [I.Call r]`. -/
noncomputable def callOkI : PrimRequest → Bool := fun r => decide (I.Call r)

theorem callOkI_iff (r : PrimRequest) : callOkI (I := I) r = true ↔ I.Call r := by
  unfold callOkI; simp

variable (S : UnionSetup I)

/-- **The front's checks on a decoded guess**: the oracle's size, the atom test, the grid signs, every scheduled
call admissible. -/
def GoodG {N : ℕ} {z : BitInput N} (g : UnionGuess S z) : Prop :=
  g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) ∧ PlanW3.AtomsOkG g ∧
    (g.checkData g.translation).signsOk = true ∧ (g.checkData g.translation).schedule.all (callOkI (I := I)) = true

/-- The setup facts the reference reads: the grid mass is a positive integer, the grid is nonempty. -/
structure GridFacts : Prop where
  mass : ∀ q, ∃ Λ : ℕ, 1 ≤ Λ ∧ S.gridMass q = Λ
  size : ∀ q, 1 ≤ S.gridSize q

variable {S}

theorem calls_of_all (D : UnionCheckData) (h : D.schedule.all (callOkI (I := I)) = true) :
    (∀ t ∈ D.termsV, I.Call t.2) ∧ (∀ t ∈ D.termsQ, I.Call t.2) ∧ (∀ t ∈ D.termsMu, I.Call t.2) := by
  have key : ∀ r ∈ D.schedule, I.Call r := fun r hr => (callOkI_iff r).1 (List.all_eq_true.1 h r hr)
  refine ⟨fun t ht => key _ ?_, fun t ht => key _ ?_, fun t ht => key _ ?_⟩ <;>
    exact List.mem_map_of_mem (f := Prod.snd) (by simp [ht])

theorem mass_ne (hF : GridFacts S) {N : ℕ} {z : BitInput N} (g : UnionGuess S z) :
    (g.checkData g.translation).mass ≠ 0 := by
  obtain ⟨Λ, hΛ, e⟩ := hF.mass g.q
  show S.gridMass g.q ≠ 0
  rw [e]; exact_mod_cast (show Λ ≠ 0 by omega)

theorem s_ne (hF : GridFacts S) {N : ℕ} {z : BitInput N} (g : UnionGuess S z) : (g.checkData g.translation).s ≠ 0 := by
  have := hF.size g.q
  show S.gridSize g.q ≠ 0
  omega

/-- The machine-order terms are admissible calls. -/
theorem my_calls (hF : GridFacts S) {N : ℕ} {z : BitInput N} (g : UnionGuess S z)
    (h : (g.checkData g.translation).schedule.all (callOkI (I := I)) = true) :
    (∀ t ∈ myV (g.checkData g.translation), I.Call t.2) ∧ (∀ t ∈ myQ (g.checkData g.translation), I.Call t.2) ∧
      (∀ t ∈ myMu (g.checkData g.translation), I.Call t.2) := by
  obtain ⟨hV, hQ, hM⟩ := calls_of_all _ h
  have hm := mass_ne hF g
  have hs := s_ne hF g
  exact ⟨fun t ht => hV t ((termsV_perm _ hm hs).mem_iff.2 ht), fun t ht => hQ t ((termsQ_perm _ hm hs).mem_iff.2 ht),
    fun t ht => hM t ((termsMu_perm _ hm hs).mem_iff.2 ht)⟩

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

variable (S)

/-- The slack thresholds of a check data at precision `p` (`accStart_eq`). -/
noncomputable def accStart (D : UnionCheckData) (p : ℕ) : Fin 6 → ℕ :=
  threshAcc ⌊scaleVQ D p * (2 * S.params.v0 + slackOf D.mass p)⌋ ⌊scaleVQ D p * (1 + S.params.v0 + slackOf D.mass p)⌋
    ⌈scaleMu D p * (S.params.threshold - slackOf D.mass p)⌉

/-- **The valid branch**: the table writer's table, the slack thresholds, `p = unionBits q`, the capacities. -/
noncomputable def goodOut (hF : GridFacts S) {N : ℕ} {z : BitInput N} (g : UnionGuess S z)
    (h : (g.checkData g.translation).schedule.all (callOkI (I := I)) = true) (cap R Lg : ℕ) : FrontOut I :=
  let D := g.checkData g.translation
  let T := tableAll D.s (myV D) (myQ D) (myMu D) (my_calls hF g h).1 (my_calls hF g h).2.1 (my_calls hF g h).2.2
  ⟨T, accStart S D (unionBits g.q), unionBits g.q, cap, R, Lg, maxMag T, maxW T⟩

open Classical in
/-- **The front's reference output.** -/
noncomputable def outRef (hF : GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N)
    (w : List Bool) : FrontOut I :=
  if h : onset ≤ N ∧ ∃ g, decodeGuess S x w = some g ∧ GoodG S g then
    goodOut S hF (Classical.choose h.2) (Classical.choose_spec h.2).2.2.2.2 (capF N) (RF N) (LgF N)
  else FrontGate.rejOut

end Out

/-! ## The decision -/

section Sem
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)
  (S : UnionSetup I)

/-- **The valid branch decides by the slack check** (`decision_slack` at the table writer's order). -/
theorem goodOut_decision (hF : GridFacts S) {N : ℕ} {z : BitInput N} (g : UnionGuess S z) (hg : GoodG S g)
    (cap R Lg : ℕ) :
    decisionOf ((goodOut S hF g hg.2.2.2 cap R Lg).keptEnd P).acc =
      slackCheck (g.checkData g.translation) (UnionGuessSlack.roundedVal P unionBits g.q) S.params.v0 S.params.threshold
        (slackOf (S.gridMass g.q) (unionBits g.q)) (callOkI (I := I)) := by
  obtain ⟨Λ, -, e⟩ := hF.mass g.q
  obtain ⟨hV, hQ, hM⟩ := calls_of_all (g.checkData g.translation) hg.2.2.2
  have hm := mass_ne hF g
  have hs := s_ne hF g
  show decisionOf (Sched.accOf P (unionBits g.q) (accStart S (g.checkData g.translation) (unionBits g.q))
    (tableAll (g.checkData g.translation).s (myV (g.checkData g.translation)) (myQ (g.checkData g.translation))
      (myMu (g.checkData g.translation)) (my_calls hF g hg.2.2.2).1 (my_calls hF g hg.2.2.2).2.1
        (my_calls hF g hg.2.2.2).2.2)
    (tableAll (g.checkData g.translation).s (myV (g.checkData g.translation)) (myQ (g.checkData g.translation))
      (myMu (g.checkData g.translation)) (my_calls hF g hg.2.2.2).1 (my_calls hF g hg.2.2.2).2.1
        (my_calls hF g hg.2.2.2).2.2).length) = _
  unfold accStart
  rw [tableAll_perm_decision P (g.checkData g.translation).s (unionBits g.q) _ _ _ _ _ _ _ _ _ _ _ _ hV hQ hM
    (termsV_perm _ hm hs).symm (termsQ_perm _ hm hs).symm (termsMu_perm _ hm hs).symm]
  exact decision_slack P (g.checkData g.translation) Λ e (hF.size g.q) (unionBits g.q) S.params.v0
    S.params.threshold (slackOf (S.gridMass g.q) (unionBits g.q)) (callOkI (I := I)) hV hQ hM hg.2.2.1 hg.2.2.2

/-- **The front's decision is the worker's meaning with the atom test.** -/
theorem outRef_sem (hF : GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N) (w : List Bool)
    (hw : w.length = N / 16) :
    decisionOf ((outRef S hF onset capF RF LgF N x w).keptEnd P).acc = true ↔
      PlanW3.workerMeaning2 S P onset (callOkI (I := I)) N x w := by
  unfold outRef
  split_ifs with h
  · obtain ⟨hon, hex⟩ := h
    have hg0 := Classical.choose_spec hex
    rw [goodOut_decision P S hF _ hg0.2]
    generalize Classical.choose hex = g at hg0 ⊢
    have hg := hg0
    unfold PlanW3.workerMeaning2 unionSlackRun
    rw [hg.1]
    simp only [unionSlackCheck]
    have hsz : decide (g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N)) = true :=
      decide_eq_true hg.2.1
    have hwd : decide (g.word.length ≤ N / 16) = true :=
      decide_eq_true (word_le_of_decodeGuess hg.1 hw.le)
    have hat : PlanW3.atomsOk S x w := fun g' h' => by
      rw [hg.1] at h'
      cases h'
      exact hg.2.2.1
    rw [hsz, hwd]
    simp [hon, hat]
  · rw [FrontGate.rejOut_keptEnd]
    simp only [FrontGate.rejKept]
    rw [FrontGate.decision_rej]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨hon, hat, hrun⟩
    apply h
    refine ⟨hon, ?_⟩
    unfold unionSlackRun at hrun
    split at hrun
    · simp at hrun
    · rename_i g hdec
      refine ⟨g, hdec, ?_⟩
      unfold unionSlackCheck slackCheck at hrun
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrun
      exact ⟨hrun.1.1, hat g hdec, hrun.2.1.1.1.1, hrun.2.1.1.1.2⟩

/-! ## The table's length, the rejecting branch, the capacity -/

theorem tableAll_length (s : ℕ) (TV TQ TM : List (ℚ × PrimRequest)) (hV : ∀ t ∈ TV, I.Call t.2)
    (hQ : ∀ t ∈ TQ, I.Call t.2) (hM : ∀ t ∈ TM, I.Call t.2) :
    (tableAll s TV TQ TM hV hQ hM).length = TV.length + TQ.length + TM.length := by
  simp [tableAll, Bridge.tableOfTerms]
  omega

/-- **The table is no longer than the decoded guess's schedule.** -/
theorem outRef_len (hF : GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N) (w : List Bool)
    (hne : (outRef S hF onset capF RF LgF N x w).table ≠ []) :
    ∃ g : UnionGuess S x, g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N) ∧
      (outRef S hF onset capF RF LgF N x w).table.length ≤ (g.checkData g.translation).schedule.length := by
  unfold outRef at hne ⊢
  split_ifs with h
  · obtain ⟨-, hex⟩ := h
    have hg := Classical.choose_spec hex
    refine ⟨Classical.choose hex, hg.2.1, ?_⟩
    have hm := mass_ne hF (Classical.choose hex)
    have hs := s_ne hF (Classical.choose hex)
    show (tableAll _ _ _ _ _ _ _).length ≤ _
    rw [tableAll_length, ← (termsV_perm _ hm hs).length_eq, ← (termsQ_perm _ hm hs).length_eq,
      ← (termsMu_perm _ hm hs).length_eq]
    simp [UnionCheckData.schedule]
    omega
  · rw [dif_neg h] at hne
    exact absurd rfl hne

/-- **Below the onset the front rejects outright.** -/
theorem outRef_rej (hF : GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N) (w : List Bool)
    (hN : N < onset) :
    (outRef S hF onset capF RF LgF N x w).table = [] ∧ (outRef S hF onset capF RF LgF N x w).cap = 1 := by
  unfold outRef
  rw [dif_neg (fun h => absurd h.1 (by omega))]
  exact ⟨rfl, rfl⟩

theorem outRef_capPos (hF : GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (hc : ∀ N, 1 ≤ capF N) (N : ℕ)
    (x : BitInput N) (w : List Bool) : 1 ≤ (outRef S hF onset capF RF LgF N x w).cap := by
  unfold outRef
  split_ifs
  · exact hc N
  · exact le_rfl

end Sem

end NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef
