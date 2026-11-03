import W3.Draft.C3Front
import Proof.CaseAnalysis.RowsGatePair
import Proof.Amplification.RecoveryCursorCalls
import Proof.MachineModel.OrdinaryMatrixPacketBranch

/-!
# The cold front end, part 8: the gated tail (generic in the cold prefix)

The near-cubic-wires paper + C.10: on a passing branch the request of `H_B` is handed to Fact C.2's algorithm (proof 1's live
Case-2 dock `CloseoutCaseTwo.NativeSourceDock.last`, the `RequestSource` cache) and the one-time policy fields are
computed (`SourcePolicy.Call`); on a rejecting branch nothing runs. One `CloseoutRowsGateColdPair` gate on the prefix's
flag, exactly as proof 1's `NativePipeline` (`WitnessNativePipeline.lean`), with the prefix any ready run.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairRepresentation

namespace W3.NearCubicWires.RepairSource.Outer3.Pipe

/-- A ready run, with blank extra tapes appended. -/
theorem ready_embed {t e s n : ℕ} {p : Machine t s} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p n input output) :
    ClockJoin.ReadyRun (TapeEmbedding.machine e p) n (Fin.addCases input (fun _ => []))
      (Fin.addCases output (fun _ => [])) := by
  obtain ⟨r, hr, ht, hh, hsteps⟩ := h
  have he := TapeEmbedding.run_embed p (fun _ : Fin e => 0) (fun _ => []) n _ r hr
  have hi : TapeEmbedding.config (fun _ : Fin e => 0) (fun _ => []) (initialConfiguration p input) =
      initialConfiguration (TapeEmbedding.machine e p) (Fin.addCases input (fun _ => [])) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := e) (fun _ => ?_) (fun _ => ?_) i
      all_goals simp [TapeEmbedding.config, initialConfiguration]
    · rfl
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (fun _ : Fin e => 0) (fun _ => []) r, he, ?_, ?_, hsteps⟩
  · simp only [TapeEmbedding.receipt, TapeEmbedding.config, ht]
  · intro i
    refine Fin.addCases (m := t) (n := e) (motive := fun j =>
      (TapeEmbedding.receipt (fun _ : Fin e => 0) (fun _ => []) r).final.heads j = 0) ?_ ?_ i
    · intro j; simpa [TapeEmbedding.receipt, TapeEmbedding.config] using hh j
    · intro j; simp [TapeEmbedding.receipt, TapeEmbedding.config]

section Pipe
variable (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ) {T0 s0 : ℕ}

abbrev RSt := CloseoutCaseTwo.RequestSource.tapes a
abbrev EPt := W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.extra D

/-- An old tape of the prefix inside the whole bank. -/
abbrev NT (T0 : ℕ) := CloseoutCaseTwo.NativeSourceDock.tapes a T0
def o1 (i : Fin T0) : Fin (NT a T0) := CloseoutCaseTwo.NativeSourceDock.oldSlots a i
def o2 (i : Fin (NT a T0)) : Fin (NT a T0 + EPt D) := i.castAdd (EPt D)

/-- The prefix with the source dock's blank tapes appended. -/
noncomputable def innerM (P0 : Machine T0 s0) : Machine (NT a T0) s0 := TapeEmbedding.machine (RSt a) P0

variable (field size arity flag : Fin T0)

/-- Cache slot `j` of the source dock. -/
noncomputable def cacheIn (j : Fin 19) : Fin (NT a T0) :=
  CloseoutCaseTwo.NativeSourceDock.slots a field size arity
    (CloseoutCaseTwo.RequestSource.cacheSlots a (CloseoutCaseTwo.SourceCache.cacheSlots a j))

/-- The policy's two inputs: cache slots `0` (`pcppOutput`) and `13` (the arity template). -/
noncomputable def polFields : Fin 2 → Fin (NT a T0) := ![cacheIn a field size arity 0, cacheIn a field size arity 13]

noncomputable def pipeFirst (P0 : Machine T0 s0) := TapeEmbedding.machine (EPt D) (innerM a P0)
noncomputable def pipeSecond :=
  Composition.machine (TapeEmbedding.machine (EPt D) (CloseoutCaseTwo.NativeSourceDock.last a field size arity))
    (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.machine D copies delta
      (polFields a field size arity))
def pipeTest (bits : Fin (NT a T0 + EPt D) → Bool) : Bool := bits (o2 a D (o1 a flag))

/-- **The gated machine.** -/
noncomputable def pipe (P0 : Machine T0 s0) :=
  CloseoutRowsGateColdPair.machine (pipeFirst a D P0) (pipeSecond a D copies delta field size arity) (pipeTest a D flag)

def pipeIn (input : Fin T0 → List Bool) : Fin (NT a T0 + EPt D) → List Bool :=
  Fin.addCases (motive := fun _ => List Bool) (CloseoutCaseTwo.NativeSourceDock.input a input) (fun _ => [])

theorem pipeIn_old (input : Fin T0 → List Bool) (i : Fin T0) : pipeIn a D input (o2 a D (o1 a i)) = input i := by
  simp [pipeIn, o1, o2, CloseoutCaseTwo.NativeSourceDock.oldSlots, CloseoutCaseTwo.NativeSourceDock.input]

/-- **Rejecting branch**: the flag is `false`, nothing runs after the prefix. -/
theorem pipe_rej (P0 : Machine T0 s0) (fuel : ℕ) (input out : Fin T0 → List Bool)
    (hP : ClockJoin.ReadyRun P0 fuel input out) (hfl : out flag = [false]) :
    ClockJoin.ReadyRun (pipe a D copies delta field size arity flag P0) (fuel + 1) (pipeIn a D input)
      (pipeIn a D out) := by
  have h0 : ClockJoin.ReadyRun (innerM a P0) fuel (CloseoutCaseTwo.NativeSourceDock.input a input)
      (CloseoutCaseTwo.NativeSourceDock.input a out) := ready_embed hP
  have h1 := ready_embed (e := EPt D) h0
  refine CloseoutRowsGateColdPair.rejected _ _ _ fuel _ _ h1 ?_
  change readTapeBit (pipeIn a D out (o2 a D (o1 a flag))) 0 = false
  rw [pipeIn_old, hfl]; rfl

end Pipe

section Live
variable (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ) {T0 s0 : ℕ} (field size arity flag : Fin T0)

theorem dock_input (out : Fin T0 → List Bool) (descriptor : List Bool) (sz ar : ℕ)
    (hf : out field = frame descriptor) (hs : out size = List.replicate sz true)
    (ha : out arity = List.replicate ar true) (j : Fin (RSt a)) :
    CloseoutCaseTwo.NativeSourceDock.input a out (CloseoutCaseTwo.NativeSourceDock.slots a field size arity j) =
      CloseoutCaseTwo.RequestSource.input a descriptor sz ar j := by
  unfold CloseoutCaseTwo.NativeSourceDock.slots CloseoutCaseTwo.RequestSource.input
  split_ifs with h0 h21 h19
  · simp only [CloseoutCaseTwo.NativeSourceDock.oldSlots, CloseoutCaseTwo.NativeSourceDock.input, Fin.addCases_left]
    exact hf
  · simp only [CloseoutCaseTwo.NativeSourceDock.oldSlots, CloseoutCaseTwo.NativeSourceDock.input, Fin.addCases_left]
    exact hs
  · simp only [CloseoutCaseTwo.NativeSourceDock.oldSlots, CloseoutCaseTwo.NativeSourceDock.input, Fin.addCases_left]
    exact ha
  · simp only [CloseoutCaseTwo.NativeSourceDock.input, Fin.addCases_right]

theorem slots_ne_old (i : Fin T0) (h1 : i ≠ field) (h2 : i ≠ size) (h3 : i ≠ arity) :
    ∀ j, CloseoutCaseTwo.NativeSourceDock.slots a field size arity j ≠ o1 a i := by
  intro j he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have e1 : i.val ≠ field.val := fun h => h1 (Fin.ext h)
  have e2 : i.val ≠ size.val := fun h => h2 (Fin.ext h)
  have e3 : i.val ≠ arity.val := fun h => h3 (Fin.ext h)
  unfold CloseoutCaseTwo.NativeSourceDock.slots at hv
  split_ifs at hv <;> simp [CloseoutCaseTwo.NativeSourceDock.oldSlots, o1] at hv <;> omega

/-- **Passing branch**: the prefix's flag is `true` and its field/size/arity tapes hold the request of `r`; the source
dock caches Fact C.2's output and the policy computes its one-time fields. -/
theorem pipe_live (P0 : Machine T0 s0) (fuel : ℕ) (input out : Fin T0 → List Bool)
    (hP : ClockJoin.ReadyRun P0 fuel input out) (hfl : out flag = [true])
    (hfs : field ≠ size) (hfa : field ≠ arity) (hsa : size ≠ arity) (hD : 1 ≤ D)
    (r : PCPPRequest a.minimumArity) (hf : out field = frame (PCPPNative.descriptor r.circuit))
    (hs : out size = List.replicate r.circuit.size true) (ha : out arity = List.replicate r.arity true) :
    ∃ actual, run (pipe a D copies delta field size arity flag P0)
        (fuel + 1 + (CloseoutCaseTwo.RequestSource.budget a r + 1 +
          W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget D copies r.arity
            (a.output r).systematicBits (a.output r).auxiliaryBits (a.output r).clauseBits delta) + 1)
        (pipeIn a D input) = some actual ∧
      actual.steps ≤ fuel + 1 + (CloseoutCaseTwo.RequestSource.budget a r + 1 +
          W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget D copies r.arity
            (a.output r).systematicBits (a.output r).auxiliaryBits (a.output r).clauseBits delta) + 1 ∧
      (∀ j : Fin 19, actual.final.tapes (o2 a D (cacheIn a field size arity j)) =
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j) ∧
      (∀ j : Fin 19, actual.final.heads (o2 a D (cacheIn a field size arity j)) = PCPPQueryClauseReuse.heads j) ∧
      W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.Fields D copies delta
        (polFields a field size arity) r (a.output r) actual.final ∧
      (∀ i : Fin T0, i ≠ field → i ≠ size → i ≠ arity →
        actual.final.tapes (o2 a D (o1 a i)) = out i ∧ actual.final.heads (o2 a D (o1 a i)) = 0) := by
  -- the prefix, lifted
  have h0 : ClockJoin.ReadyRun (innerM a P0) fuel (CloseoutCaseTwo.NativeSourceDock.input a input)
      (CloseoutCaseTwo.NativeSourceDock.input a out) := ready_embed hP
  obtain ⟨lifted, hl, hlt, hlh, hls⟩ := ready_embed (e := EPt D) h0
  -- the source dock
  obtain ⟨base, hb, bs, bt, bh, -, -⟩ := CloseoutCaseTwo.RequestSource.source_run a r
  obtain ⟨res, hres, -, rs, rh, rt, raway⟩ := RecoveryFocus.dock
    (CloseoutCaseTwo.NativeSourceDock.slots a field size arity)
    (CloseoutCaseTwo.NativeSourceDock.slots_injective a field size arity hfs hfa hsa)
    (CloseoutCaseTwo.RequestSource.machine a) _ (fun _ => 0)
    (CloseoutCaseTwo.NativeSourceDock.input a out)
    (initialConfiguration (CloseoutCaseTwo.RequestSource.machine a)
      (CloseoutCaseTwo.RequestSource.input a (PCPPNative.descriptor r.circuit) r.circuit.size r.arity))
    (fun _ => rfl) (fun j => dock_input a field size arity out _ _ _ hf hs ha j) base hb
  have e1 := TapeEmbedding.run_embed (CloseoutCaseTwo.NativeSourceDock.last a field size arity)
    (fun _ : Fin (EPt D) => 0) (fun _ => []) _ _ res hres
  -- the policy
  have hh0 : res.final.heads (polFields a field size arity 0) = 0 := (rh _).trans (bh 0)
  have hh1 : res.final.heads (polFields a field size arity 1) = 1 := (rh _).trans (bh 13)
  have ht0 : res.final.tapes (polFields a field size arity 0) = pcppOutput r (a.output r) := (rt _).trans (bt 0)
  have ht1 : res.final.tapes (polFields a field size arity 1) = UnaryTemplate.tape r.arity := (rt _).trans (bt 13)
  have hinj : Function.Injective (polFields a field size arity) := by
    have distinct : polFields a field size arity 0 ≠ polFields a field size arity 1 := by
      intro he; rw [he, hh1] at hh0; omega
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (distinct he)
    · exact False.elim (distinct he.symm)
    · rfl
  obtain ⟨pol, hpol, ps, pkeep, pf⟩ := W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.call_run
    D copies delta (polFields a field size arity) hinj res.final.tapes res.final.heads r (a.output r) hD hh0 hh1 ht0 ht1
  -- the second machine, from the restart of the lifted prefix
  have e1' : runFrom (TapeEmbedding.machine (EPt D) (CloseoutCaseTwo.NativeSourceDock.last a field size arity))
      (CloseoutCaseTwo.RequestSource.budget a r)
      ⟨(TapeEmbedding.machine (EPt D) (CloseoutCaseTwo.NativeSourceDock.last a field size arity)).start,
        lifted.final.heads, lifted.final.tapes⟩ =
      some (TapeEmbedding.receipt (fun _ : Fin (EPt D) => 0) (fun _ => []) res) := by
    convert e1 using 2
    apply configuration_ext
    · rfl
    · funext i; rw [hlh i]
      refine Fin.addCases (m := NT a T0) (n := EPt D) (fun _ => ?_) (fun _ => ?_) i
      · simp only [TapeEmbedding.config, Fin.addCases_left]
      · simp only [TapeEmbedding.config, Fin.addCases_right]
    · rw [hlt]; rfl
  have he := MatrixPacketBranch.restart_fields (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.machine
    D copies delta (polFields a field size arity)) (TapeEmbedding.receipt (fun _ : Fin (EPt D) => 0) (fun _ => []) res).final
    (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.heads D res.final.heads)
    (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.input D res.final.tapes) rfl rfl
  dsimp only [RecoveryCalls.restarted] at he
  rw [he] at hpol
  have e2 := Composition.run_join (TapeEmbedding.machine (EPt D) (CloseoutCaseTwo.NativeSourceDock.last a field size arity))
    (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.machine D copies delta (polFields a field size arity))
    _ _ _ _ pol e1' hpol
  have hfirst : runFrom (pipeFirst a D P0) fuel (initialConfiguration (pipeFirst a D P0) (pipeIn a D input)) =
      some lifted := hl
  have hrs : res.steps ≤ CloseoutCaseTwo.RequestSource.budget a r := rs ▸ bs
  have scanned : pipeTest a D flag lifted.final.scanned = true := by
    change readTapeBit (lifted.final.tapes (o2 a D (o1 a flag))) (lifted.final.heads (o2 a D (o1 a flag))) = true
    have h1 := hlh (o2 a D (o1 a flag))
    have h2 : lifted.final.tapes (o2 a D (o1 a flag)) = [true] := by
      rw [hlt]; exact (pipeIn_old a D out flag).trans hfl
    rw [h1, h2]; rfl
  obtain ⟨u, hu, initial⟩ := call_receipt _
    (CloseoutRowsGateColdPair.programs (pipeFirst a D P0) (pipeSecond a D copies delta field size arity)) 0
    (CloseoutRowsGateColdPair.next (pipeTest a D flag)) 0 1 fuel _ lifted hl (by
      change (if pipeTest a D flag lifted.final.scanned then some (1 : Fin 2) else none) = some 1
      rw [scanned]; rfl)
  obtain ⟨v, hv, terminal⟩ := stop_receipt _
    (CloseoutRowsGateColdPair.programs (pipeFirst a D P0) (pipeSecond a D copies delta field size arity)) 0
    (CloseoutRowsGateColdPair.next (pipeTest a D flag)) 1 _ _ _ e2 (by rfl)
  obtain ⟨actual, ha, hfinal, hsteps⟩ := (initial.trans terminal).run (by
    simp only [RecoveryCalls.machine, RecoveryCalls.stopped, Equiv.symm_apply_apply, Option.isNone_none])
  set Ftot := fuel + 1 + (CloseoutCaseTwo.RequestSource.budget a r + 1 +
      W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget D copies r.arity
        (a.output r).systematicBits (a.output r).auxiliaryBits (a.output r).clauseBits delta) + 1 with hFtot
  have hb : u + v ≤ Ftot := by omega
  have more := run_moreFuel (pipe a D copies delta field size arity flag P0) (u + v) (Ftot - (u + v))
    (pipeIn a D input) actual ha
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨actual, more, hsteps.le.trans hb, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hfinal]
    exact (pkeep _).2.trans ((rt _).trans (bt j))
  · intro j
    rw [hfinal]
    exact (pkeep _).1.trans ((rh _).trans (bh j))
  · rw [hfinal]
    exact ⟨pf.count, pf.clause, pf.q0, pf.cap, pf.cursor⟩
  · intro i h1 h2 h3
    obtain ⟨ah, at'⟩ := raway (o1 a i) (slots_ne_old a field size arity i h1 h2 h3)
    rw [hfinal]
    refine ⟨(pkeep _).2.trans (at'.trans ?_), (pkeep _).1.trans ah⟩
    simp [o1, CloseoutCaseTwo.NativeSourceDock.oldSlots, CloseoutCaseTwo.NativeSourceDock.input]

end Live

end W3.NearCubicWires.RepairSource.Outer3.Pipe
