import W3.Front.ColdRun
import W3.Front.ColdPipe
import W3.Front.Main
import W3.Front.ColdBound

/-!
# The cold front end, part 9: `ColdNativeW` — the producer `coldNativeW_of`

The machine: the rewound compiled cold prefix `coldP` (`Front.cold_exec_pow` / `cold_exec_rej` + `readyRewound`),
then the gated tail `Pipe.pipe` (proof 1's `NativeSourceDock.last` + `SourcePolicy.Call`, `pipe_live` / `pipe_rej`).
`F = frontD`. The original input tape is tape `2` (D11, `coldNativeW_of_originalTape`): the input stream `X` itself,
never written. Onset `max 1 (minimum arity)`; the index guard `c* = max cutoff (max onset SV.onset)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec

namespace W3.NearCubicWires.RepairSource.Outer3.ColdW

open Front Pipe

section W
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)

/-- The producer's onset: past `F`'s onset (`1`) and Fact C.2's minimum arity (so `requestAt = requestOf`). -/
def onsetW : ℕ := max 1 a.minimumArity
/-- The index guard. -/
def cstarW : ℕ := max cutoff (max (onsetW a) SV.onset)

noncomputable abbrev NSW := NSC mw SV (frontD mw SV) degree
noncomputable abbrev T0W := NSW mw SV degree + 2 + nrW + 1
noncomputable abbrev P0W := Rewind.machine (coldP mw SV (frontD mw SV) degree (cstarW SV a cutoff)).compile

/-- Stream `i` of the cold prefix, as a tape of the rewound compiled machine. -/
noncomputable def slW (i : Fin (NSW mw SV degree + 1)) : Fin (T0W mw SV degree) := Fin.castAdd 1 (sTape (nr := nrW) i)
theorem slW_val (i : Fin (NSW mw SV degree + 1)) : (slW mw SV degree i).val = if i.val = 0 then 0 else i.val + 1 := rfl

noncomputable abbrev fW := slW mw SV degree (mF (progB mw SV) (progU mw SV) (Dc degree) (frontD mw SV) (frontD mw SV).field)
noncomputable abbrev sW := slW mw SV degree (mF (progB mw SV) (progU mw SV) (Dc degree) (frontD mw SV) (frontD mw SV).sizeSlot)
noncomputable abbrev aW := slW mw SV degree (mF (progB mw SV) (progU mw SV) (Dc degree) (frontD mw SV) (frontD mw SV).aritySlot)
noncomputable abbrev flW := slW mw SV degree (cFL _ _ _ _)
noncomputable abbrev lnW := slW mw SV degree (cLEN _ _ _ _)
noncomputable abbrev xW := slW mw SV degree (cX _ _ _ _)

theorem mFv (j : Fin (frontD mw SV).t) (h0 : j.val ≠ 0) (h4 : j.val ≠ 4) (h6 : j.val ≠ 6) :
    (mF (progB mw SV) (progU mw SV) (Dc degree) (frontD mw SV) j).val =
      bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) + j.val := by
  rw [mF_val]
  rw [if_neg (fun e => h0 (by rw [e]; rfl)), if_neg (fun e => h4 (by rw [e]; rfl)), if_neg (fun e => h6 (by rw [e]; rfl))]

theorem fW_val : (fW mw SV degree).val = bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) + 8 := by
  have h := mFv mw SV degree (frontD mw SV).field (by show (7:ℕ) ≠ 0; decide) (by show (7:ℕ) ≠ 4; decide)
    (by show (7:ℕ) ≠ 6; decide)
  have h7 : (frontD mw SV).field.val = 7 := rfl
  rw [slW_val, h, h7, if_neg (by omega)]
theorem sW_val : (sW mw SV degree).val = bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) + 9 := by
  have h := mFv mw SV degree (frontD mw SV).sizeSlot (by show (8:ℕ) ≠ 0; decide) (by show (8:ℕ) ≠ 4; decide)
    (by show (8:ℕ) ≠ 6; decide)
  have h7 : (frontD mw SV).sizeSlot.val = 8 := rfl
  rw [slW_val, h, h7, if_neg (by omega)]
theorem aW_val : (aW mw SV degree).val = bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) + 10 := by
  have h := mFv mw SV degree (frontD mw SV).aritySlot (by show (9:ℕ) ≠ 0; decide) (by show (9:ℕ) ≠ 4; decide)
    (by show (9:ℕ) ≠ 6; decide)
  have h7 : (frontD mw SV).aritySlot.val = 9 := rfl
  rw [slW_val, h, h7, if_neg (by omega)]
theorem bF_ge : 33 ≤ bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) := by unfold bF; omega

end W

section Sem
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)

/-- At `n = 2^ν`, `Passes` is the index guard plus `PassCore`. -/
theorem passes_pow_iff (ν : ℕ) (x : BitInput (2 ^ ν)) (raw : List Bool) :
    Passes mw SV cutoff (onsetW a) degree x raw ↔ cstarW SV a cutoff ≤ ν ∧ PassCore mw SV degree ν x raw := by
  have hl : Nat.log 2 (2 ^ ν) = ν := Nat.log_pow (by norm_num) ν
  unfold Passes PassCore Guard cstarW
  rw [hl]
  constructor
  · rintro ⟨-, h1, h2, h3, B, hd, hs, hp, hf, hc⟩
    exact ⟨by omega, B, hd, hs, hp, hf, (Outer.check_iff_checkAt ν x B.src).2 hc⟩
  · rintro ⟨h, B, hd, hs, hp, hf, hc⟩
    exact ⟨rfl, by omega, by omega, by omega, B, hd, hs, hp, hf, (Outer.check_iff_checkAt ν x B.src).1 hc⟩

theorem not_passes (n : ℕ) (hn : ∀ ν, n ≠ 2 ^ ν) (x : BitInput n) (raw : List Bool) :
    ¬ Passes mw SV cutoff (onsetW a) degree x raw := fun h => hn _ h.1

/-- The pass bit, on the input word. -/
noncomputable def passedW (xs raw : List Bool) : Bool := by
  classical
  exact decide (∃ (m : ℕ) (y : BitInput m), List.ofFn y = xs ∧ Passes mw SV cutoff (onsetW a) degree y raw)

theorem passedW_iff {n : ℕ} (x : BitInput n) (raw : List Bool) :
    passedW mw SV a cutoff degree (List.ofFn x) raw = true ↔ Passes mw SV cutoff (onsetW a) degree x raw := by
  classical
  unfold passedW
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨m, y, he, hp⟩
    have hs := List.ofFn_inj'.mp he
    obtain ⟨rfl, hy⟩ := Sigma.mk.inj_iff.mp hs
    cases hy
    exact hp
  · intro h; exact ⟨n, x, rfl, h⟩

/-- The decoded pair (any pair when the field does not decode). -/
noncomputable def guessOf (q : ℕ) (raw : List Bool) : Outer.OuterGuess q :=
  ⟨(decodeBooleanCircuit q (value (fld1 raw))).getD (Worker.defaultOracle q),
    (decodeBooleanCircuit q (value (fld2 raw))).getD (Worker.defaultOracle q)⟩

theorem guessOf_eq {q : ℕ} (raw : List Bool) (B : Outer.OuterGuess q) (h : Worker.Decodes q raw B) :
    guessOf q raw = B := by
  obtain ⟨h1, h2⟩ := h
  unfold guessOf
  rw [show value (fld1 raw) = value (Worker.Format.readField raw).1 from rfl, h1,
    show value (fld2 raw) = value (Worker.Format.readField (Worker.Format.readField raw).2).1 from rfl, h2]
  rfl

/-- The request the waist caches. -/
noncomputable def reqW (n : ℕ) (raw : List Bool) : PCPPRequest a.minimumArity :=
  requestAt mw SV a (Nat.log 2 n) (guessOf (Outer.width mw SV n) raw)

/-- The tail's fuel on a passing branch. -/
noncomputable def tailW (n : ℕ) (raw : List Bool) : ℕ :=
  CloseoutCaseTwo.RequestSource.budget a (reqW mw SV a n raw) + 1 +
    W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget D copies (reqW mw SV a n raw).arity
      (a.output (reqW mw SV a n raw)).systematicBits (a.output (reqW mw SV a n raw)).auxiliaryBits
      (a.output (reqW mw SV a n raw)).clauseBits delta

/-- **The budget**: the rewound prefix, the gate, and on a pass the source dock and the policy. -/
noncomputable def budgetW (n : ℕ) (x : BitInput n) (raw : List Bool) : ℕ :=
  (2 * coldU mw SV (frontD mw SV) degree (cstarW SV a cutoff) n raw + 2) + 1 +
    (if passedW mw SV a cutoff degree (List.ofFn x) raw = true then tailW mw SV a D copies delta n raw + 1 else 0)

end Sem

section Run
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)

/-- **The machine.** -/
noncomputable abbrev MW := pipe a D copies delta (fW mw SV degree) (sW mw SV degree) (aW mw SV degree)
  (flW mw SV degree) (P0W mw SV a cutoff degree)
noncomputable abbrev TW := NT a (T0W mw SV degree) + EPt D

/-- **The input bank.** -/
noncomputable def inW (xs raw : List Bool) : Fin (TW mw SV a D degree) → List Bool :=
  pipeIn a D (Fin.addCases (motive := fun _ => List Bool) (coldBank (startC mw SV (frontD mw SV) degree xs raw))
    (fun _ : Fin 1 => []))

noncomputable abbrev cacheW (j : Fin 19) : Fin (TW mw SV a D degree) :=
  o2 a D (cacheIn a (fW mw SV degree) (sW mw SV degree) (aW mw SV degree) j)
noncomputable abbrev polW := W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.slots D
  (polFields a (fW mw SV degree) (sW mw SV degree) (aW mw SV degree))

/-- What a run of the machine must deliver (`run`, at the bank's slots). -/
def RunConcl {s : ℕ} (M : Machine (TW mw SV a D degree) s) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (actual : ExecutionReceipt (TW mw SV a D degree) s) : Prop :=
  (passedW mw SV a cutoff degree (List.ofFn x) raw = true →
      actual.final.tapes (o2 a D (o1 a (xW mw SV degree))) = frame (List.ofFn x)) ∧
    run M (budgetW mw SV a cutoff D degree copies delta n x raw)
      (inW mw SV a D degree (List.ofFn x) raw) = some actual ∧
    actual.steps ≤ budgetW mw SV a cutoff D degree copies delta n x raw ∧
    actual.final.tapes (o2 a D (o1 a (lnW mw SV degree))) = List.replicate n true ∧
    actual.final.heads (o2 a D (o1 a (lnW mw SV degree))) = 0 ∧
    actual.final.heads (o2 a D (o1 a (flW mw SV degree))) = 0 ∧
    readTapeBit (actual.final.tapes (o2 a D (o1 a (flW mw SV degree)))) 0 =
      passedW mw SV a cutoff degree (List.ofFn x) raw ∧
    ∀ B : Outer.OuterGuess (Outer.width mw SV n), passedW mw SV a cutoff degree (List.ofFn x) raw = true →
      Worker.Decodes (Outer.width mw SV n) raw B →
      let r := requestAt mw SV a (Nat.log 2 n) B
      (∀ j : Fin 19, actual.final.tapes (cacheW mw SV a D degree j) =
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j) ∧
      (∀ j : Fin 19, actual.final.heads (cacheW mw SV a D degree j) = PCPPQueryClauseReuse.heads j) ∧
      PolicyAt D copies delta (polW mw SV a D degree) r (a.output r) actual.final

theorem slot_facts :
    fW mw SV degree ≠ sW mw SV degree ∧ fW mw SV degree ≠ aW mw SV degree ∧ sW mw SV degree ≠ aW mw SV degree ∧
    (∀ i : Fin (T0W mw SV degree), i.val < 33 → i ≠ fW mw SV degree ∧ i ≠ sW mw SV degree ∧ i ≠ aW mw SV degree) := by
  have h1 := fW_val mw SV degree
  have h2 := sW_val mw SV degree
  have h3 := aW_val mw SV degree
  have h4 := bF_ge mw SV degree
  refine ⟨Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega), fun i hi =>
    ⟨Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega), Fin.ne_of_val_ne (by omega)⟩⟩

theorem cstar_facts : 1 ≤ cstarW SV a cutoff ∧ (frontD mw SV).onset ≤ cstarW SV a cutoff ∧
    a.minimumArity ≤ cstarW SV a cutoff := by
  rw [frontD_onset]; unfold cstarW onsetW; omega

/-- A rejecting prefix (flag `false`) gives the run. -/
theorem run_rej {n : ℕ} (x : BitInput n) (raw : List Bool)
    (hp : passedW mw SV a cutoff degree (List.ofFn x) raw = false)
    (τ : WState (NSW mw SV degree) nrW) (cap : ℕ)
    (e : WXExec cap (coldP mw SV (frontD mw SV) degree (cstarW SV a cutoff))
      (startC mw SV (frontD mw SV) degree (List.ofFn x) raw) τ (coldU mw SV (frontD mw SV) degree (cstarW SV a cutoff) n raw))
    (hFL : τ.st (cFL _ _ _ _) = [false]) (hLEN : τ.st (cLEN _ _ _ _) = List.replicate n true) :
    ∃ actual, RunConcl mw SV a cutoff D degree copies delta (MW mw SV a cutoff D degree copies delta) x raw actual := by
  obtain ⟨out, hready, hout⟩ := WXExec.readyRewound e (fun _ => rfl) (fun _ => rfl) rfl
  obtain ⟨r, hr, ht, hh, hs⟩ := pipe_rej a D copies delta (fW mw SV degree) (sW mw SV degree) (aW mw SV degree)
    (flW mw SV degree) (P0W mw SV a cutoff degree) _ _ out hready ((hout _).trans hFL)
  have hb : budgetW mw SV a cutoff D degree copies delta n x raw =
      2 * coldU mw SV (frontD mw SV) degree (cstarW SV a cutoff) n raw + 2 + 1 := by
    unfold budgetW; rw [hp]; simp
  refine ⟨r, (fun h => by simp [hp] at h), (by rw [hb]; exact hr), (by rw [hb]; exact hs), ?_, hh _, hh _, ?_,
    (fun B h => by simp [hp] at h)⟩
  · rw [ht, pipeIn_old]; show out ((sTape (cLEN _ _ _ _)).castAdd 1) = _; rw [hout]; exact hLEN
  · rw [ht, pipeIn_old, hp]; show readTapeBit (out ((sTape (cFL _ _ _ _)).castAdd 1)) 0 = false; rw [hout, hFL]; rfl

end Run

section RunAll
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)

theorem runW (hD : 1 ≤ D) {n : ℕ} (x : BitInput n) (raw : List Bool) (h16 : 16 * raw.length ≤ n) :
    ∃ actual, RunConcl mw SV a cutoff D degree copies delta (MW mw SV a cutoff D degree copies delta) x raw actual := by
  classical
  obtain ⟨h1c, honc, hmin⟩ := cstar_facts mw SV a cutoff
  obtain ⟨hfs, hfa, hsa, hlow⟩ := slot_facts mw SV degree
  by_cases hpow : ∃ ν, n = 2 ^ ν
  swap
  · have hn : ∀ ν, n ≠ 2 ^ ν := fun ν h => hpow ⟨ν, h⟩
    obtain ⟨τ, e, hFL, hLEN, -⟩ := cold_exec_rej mw SV (frontD mw SV) degree (cstarW SV a cutoff) hn x raw
    have hp : passedW mw SV a cutoff degree (List.ofFn x) raw = false := by
      cases h : passedW mw SV a cutoff degree (List.ofFn x) raw
      · rfl
      · exact absurd ((passedW_iff mw SV a cutoff degree x raw).1 h) (not_passes mw SV a cutoff degree n hn x raw)
    exact run_rej mw SV a cutoff D degree copies delta x raw hp τ _ e hFL hLEN
  obtain ⟨ν, rfl⟩ := hpow
  obtain ⟨τ, e, ⟨b, hb, hiff⟩, hLEN, hX, facts⟩ :=
    cold_exec_pow mw SV (frontD mw SV) degree (cstarW SV a cutoff) h1c honc ν x raw h16
  have hpb : passedW mw SV a cutoff degree (List.ofFn x) raw = b := by
    have h1 := passedW_iff mw SV a cutoff degree x raw
    rw [passes_pow_iff, ← hiff] at h1
    cases b <;> cases h : passedW mw SV a cutoff degree (List.ofFn x) raw <;> simp_all
  cases b
  · exact run_rej mw SV a cutoff D degree copies delta x raw hpb τ _ e hb hLEN
  -- the passing branch
  have hP := (passes_pow_iff mw SV a cutoff degree ν x raw).1 ((passedW_iff mw SV a cutoff degree x raw).1 hpb)
  obtain ⟨hc, hPC⟩ := hP
  obtain ⟨B, hdec, -, -, -⟩ := id hPC
  obtain ⟨hF, hS, hA⟩ := facts B hdec hc hPC
  have hl : Nat.log 2 (2 ^ ν) = ν := Nat.log_pow (by norm_num) ν
  have hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν) := by
    have := nu_lt_width mw SV ν; omega
  have hr : requestAt mw SV a (Nat.log 2 (2 ^ ν)) B = requestOf mw SV a ν B hq := by
    rw [hl]; exact requestAt_of mw SV a ν B hq
  set r := requestAt mw SV a (Nat.log 2 (2 ^ ν)) B with hrd
  obtain ⟨out, hready, hout⟩ := WXExec.readyRewound e (fun _ => rfl) (fun _ => rfl) rfl
  obtain ⟨actual, hrun, hsteps, hcache, hheads, hfields, hkeep⟩ := pipe_live a D copies delta (fW mw SV degree)
    (sW mw SV degree) (aW mw SV degree) (flW mw SV degree) (P0W mw SV a cutoff degree) _ _ out hready
    ((hout _).trans hb) hfs hfa hsa hD r
    (by rw [hr]; exact (hout _).trans hF) (by rw [hr]; exact (hout _).trans hS) (by rw [hr]; exact (hout _).trans hA)
  have hg : guessOf (Outer.width mw SV (2 ^ ν)) raw = B := guessOf_eq raw B hdec
  have hbud : budgetW mw SV a cutoff D degree copies delta (2 ^ ν) x raw =
      2 * coldU mw SV (frontD mw SV) degree (cstarW SV a cutoff) (2 ^ ν) raw + 2 + 1 +
        (CloseoutCaseTwo.RequestSource.budget a r + 1 +
          W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget D copies r.arity
            (a.output r).systematicBits (a.output r).auxiliaryBits (a.output r).clauseBits delta) + 1 := by
    unfold budgetW tailW reqW
    rw [hpb, if_pos rfl, hg, ← hrd]
    omega
  have l4 : (lnW mw SV degree).val < 33 := by show 4 < 33; decide
  have l5 : (flW mw SV degree).val < 33 := by show 5 < 33; decide
  have l2 : (xW mw SV degree).val < 33 := by show 2 < 33; decide
  have kLN := hkeep (lnW mw SV degree) (hlow _ l4).1 (hlow _ l4).2.1 (hlow _ l4).2.2
  have kFL := hkeep (flW mw SV degree) (hlow _ l5).1 (hlow _ l5).2.1 (hlow _ l5).2.2
  have kX := hkeep (xW mw SV degree) (hlow _ l2).1 (hlow _ l2).2.1 (hlow _ l2).2.2
  refine ⟨actual, fun _ => kX.1.trans ((hout _).trans hX), by rw [hbud]; exact hrun, by rw [hbud]; exact hsteps,
    kLN.1.trans ((hout _).trans hLEN), kLN.2, kFL.2, ?_, ?_⟩
  · rw [kFL.1, hpb]; show readTapeBit (out ((sTape (cFL _ _ _ _)).castAdd 1)) 0 = true; rw [hout, hb]; rfl
  · intro B' _ hB'
    have e' := decodes_unique raw B' B hB' hdec
    subst e'
    exact ⟨hcache, hheads, ⟨hfields.count, hfields.clause, hfields.q0, hfields.cap, hfields.cursor⟩⟩

end RunAll

section Layout
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)

theorem st_ge : 38 ≤ CloseoutCaseTwo.SourceCache.tapes a := by
  have := CloseoutCaseTwo.SourceCache.cold_lower a
  have e : CloseoutCaseTwo.SourceCache.tapes a = CloseoutCaseTwo.SourceCache.coldTapes a +
      CloseoutCaseTwo.SourceCall.tapes a := rfl
  omega

theorem rs_ge : 38 ≤ RSt a := by
  have := st_ge a
  have e : RSt a = CloseoutCaseTwo.SourceCache.tapes a + CloseoutCaseTwo.RequestInput.tapes := rfl
  omega

theorem cacheIn_val {T0 : ℕ} (f s ar : Fin T0) (j : Fin 19) : (cacheIn a f s ar j).val = T0 + j.val := by
  have hv : (CloseoutCaseTwo.RequestSource.cacheSlots a (CloseoutCaseTwo.SourceCache.cacheSlots a j)).val = j.val := rfl
  have hj := j.isLt
  have ht := st_ge a
  unfold cacheIn CloseoutCaseTwo.NativeSourceDock.slots
  rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), Fin.val_natAdd, hv]

theorem cacheW_val (j : Fin 19) : (cacheW mw SV a D degree j).val = T0W mw SV degree + j.val := by
  unfold cacheW o2; rw [Fin.val_castAdd]; exact cacheIn_val a _ _ _ j

theorem polW_val (i : Fin (EPt D)) : (polW mw SV a D degree i).val =
    if i.val = 0 then T0W mw SV degree else if i.val = 42 then T0W mw SV degree + 13 else NT a (T0W mw SV degree) + i.val := by
  unfold polW W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.slots
  by_cases h0 : i.val = 0
  · rw [if_pos h0, if_pos h0]
    simp only [W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.old, Fin.val_castAdd, polFields,
      Matrix.cons_val_zero]
    rw [cacheIn_val]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h42 : i.val = 42
    · rw [if_pos h42, if_pos h42]
      simp only [W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call.old, Fin.val_castAdd, polFields,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
      rw [cacheIn_val]; rfl
    · rw [if_neg h42, if_neg h42, Fin.val_natAdd]

theorem T0W_ge : 34 ≤ T0W mw SV degree := by unfold T0W NSW NSC NS nsC; omega

theorem input_eqW (x raw : List Bool) (i : Fin (TW mw SV a D degree)) :
    inW mw SV a D degree x raw i = if i.val = 3 then frame raw else if i.val = 2 then frame x else [] := by
  have h34 := T0W_ge mw SV degree
  unfold inW pipeIn CloseoutCaseTwo.NativeSourceDock.input
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
  · rw [Fin.addCases_left, Fin.val_castAdd]
    refine Fin.addCases (fun i0 => ?_) (fun i3 => ?_) i1
    · rw [Fin.addCases_left, Fin.val_castAdd]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i0
      · rw [Fin.addCases_left, Fin.val_castAdd]
        rcases tape_cases j with ⟨t, rfl⟩ | rfl | ⟨r, rfl⟩
        · rw [CheckedPCPP.coldBank_s, sTape_val]
          show (if t.val = 1 then frame x else if t.val = 2 then frame raw else []) = _
          by_cases h0 : t.val = 0
          · rw [if_pos h0, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          rw [if_neg h0]
          by_cases h1 : t.val = 1
          · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]
          · rw [if_neg h1]
            by_cases h2 : t.val = 2
            · rw [if_pos h2, if_pos (by omega)]
            · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
        · rw [CheckedPCPP.coldBank_c, cTape_val]; simp
        · rw [CheckedPCPP.coldBank_r, rTape_val]
          unfold NSW NSC NS nsC
          rw [if_neg (by omega), if_neg (by omega)]
      · rw [Fin.addCases_right, Fin.val_natAdd]
        unfold NSW NSC NS nsC
        rw [if_neg (by omega), if_neg (by omega)]
    · rw [Fin.addCases_right, Fin.val_natAdd]
      rw [if_neg (by omega), if_neg (by omega)]
  · rw [Fin.addCases_right, Fin.val_natAdd]
    have : T0W mw SV degree ≤ NT a (T0W mw SV degree) := by
      show T0W mw SV degree ≤ T0W mw SV degree + RSt a; omega
    rw [if_neg (by omega), if_neg (by omega)]

end Layout

section Bound
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)

theorem budgetW_bound (hD : 1 ≤ D) : ∃ C e : ℕ, ∀ (n : ℕ) (x : BitInput n) (raw : List Bool), 16 * raw.length ≤ n →
    budgetW mw SV a cutoff D degree copies delta n x raw ≤ C * (n + 1) ^ 2 * (Outer.width mw SV n + 1) ^ e := by
  classical
  obtain ⟨M0, hM0⟩ := Outer.natBitLength_T_le SV
  obtain ⟨d1, c1, h1⟩ := Gpre_poly mw SV (frontD mw SV) degree (cstarW SV a cutoff)
  obtain ⟨d2, c2, h2⟩ := Gtail_poly mw SV a D copies degree delta hD M0
  obtain ⟨h1c, -, hmin⟩ := cstar_facts mw SV a cutoff
  refine ⟨2 * c1 + c2 + 10, d1 + d2, fun n x raw h16 => ?_⟩
  set q := Outer.width mw SV n with hqd
  have hc := coldU_le mw SV (frontD mw SV) degree (cstarW SV a cutoff) n raw h16
  rw [← hqd] at hc
  have hg : Gpre mw SV (frontD mw SV) degree (cstarW SV a cutoff) q ≤ c1 * (q + 1) ^ d1 := h1 q
  have hQ1 : (q + 1) ^ d1 ≤ (q + 1) ^ (d1 + d2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hQ2 : (q + 1) ^ d2 ≤ (q + 1) ^ (d1 + d2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hA : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hQ : 1 ≤ (q + 1) ^ (d1 + d2) := Nat.one_le_pow _ _ (by omega)
  set X := (n + 1) ^ 2 * (q + 1) ^ (d1 + d2) with hX
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcX : coldU mw SV (frontD mw SV) degree (cstarW SV a cutoff) n raw ≤ c1 * X := by
    calc _ ≤ (n + 1) ^ 2 * Gpre mw SV (frontD mw SV) degree (cstarW SV a cutoff) q := hc
      _ ≤ (n + 1) ^ 2 * (c1 * (q + 1) ^ (d1 + d2)) :=
          Nat.mul_le_mul_left _ (hg.trans (Nat.mul_le_mul_left _ hQ1))
      _ = c1 * X := by rw [hX]; ring
  have htX : passedW mw SV a cutoff degree (List.ofFn x) raw = true →
      tailW mw SV a D copies delta n raw ≤ c2 * X := by
    intro hp
    have hP := (passedW_iff mw SV a cutoff degree x raw).1 hp
    obtain ⟨ν, hν⟩ : ∃ ν, n = 2 ^ ν := ⟨_, hP.1⟩
    subst hν
    obtain ⟨hcν, hPC⟩ := (passes_pow_iff mw SV a cutoff degree ν x raw).1 hP
    obtain ⟨B, hdec, -, hpf, -⟩ := hPC
    have hl : Nat.log 2 (2 ^ ν) = ν := Nat.log_pow (by norm_num) ν
    have hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν) := by
      have := nu_lt_width mw SV ν; omega
    have ht := tail_le mw SV a D copies degree delta M0 hM0 ν (by omega) B hq hpf
    have hreq : reqW mw SV a (2 ^ ν) raw = requestOf mw SV a ν B hq := by
      unfold reqW; rw [guessOf_eq raw B hdec, hl]; exact requestAt_of mw SV a ν B hq
    have hg2 : Gtail mw SV a D copies degree delta M0 q ≤ c2 * (q + 1) ^ d2 := h2 q
    calc tailW mw SV a D copies delta (2 ^ ν) raw ≤ Gtail mw SV a D copies degree delta M0 q := by
          unfold tailW; rw [hreq]; exact ht
      _ ≤ c2 * (q + 1) ^ d2 := hg2
      _ ≤ c2 * X := Nat.mul_le_mul_left _ (hQ2.trans (by rw [hX]; exact Nat.le_mul_of_pos_left _ (by omega)))
  have hfin : (2 * c1 + c2 + 10) * (n + 1) ^ 2 * (q + 1) ^ (d1 + d2) = 2 * (c1 * X) + c2 * X + 10 * X := by
    rw [hX]; ring
  rw [hfin]
  unfold budgetW
  split_ifs with hp
  · have := htX hp; omega
  · omega

end Bound

end W3.NearCubicWires.RepairSource.Outer3.ColdW

namespace W3.NearCubicWires.RepairSource.Outer3

open ColdW Front Pipe

/-- **The producer**: the worker's cold-native front end at `mw SV a cutoff D degree copies delta`
(paper, C.10): cold prefix (`n = 2^ν`, `ν ≥ c*`, the D6 fields read, truncated past
`L(q)` and decoded by proof 1's cold decoder on a `poly(q)` padding word, the `q^G` caps, JF's `frontD`), then the
gated source dock + policy. Needs `1 ≤ D` (the policy call). -/
noncomputable def coldNativeW_of (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
    (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) (cutoff D degree copies : ℕ) (delta : ℚ)
    (hD : 1 ≤ D) : ColdNativeW mw SV a cutoff D degree copies delta where
  tapes := TW mw SV a D degree
  st := _
  machine := MW mw SV a cutoff D degree copies delta
  input := inW mw SV a D degree
  budget := budgetW mw SV a cutoff D degree copies delta
  lengthSlot := o2 a D (o1 a (lnW mw SV degree))
  flagSlot := o2 a D (o1 a (flW mw SV degree))
  originalTape := o2 a D (o1 a (xW mw SV degree))
  cacheSlots := cacheW mw SV a D degree
  policySlots := polW mw SV a D degree
  onset := onsetW a
  passed := passedW mw SV a cutoff degree
  passed_iff := fun x raw => passedW_iff mw SV a cutoff degree x raw
  run := fun x raw h => by
    obtain ⟨act, hact⟩ := runW mw SV a cutoff D degree copies delta hD x raw h
    exact ⟨act, hact⟩
  budget_bound := budgetW_bound mw SV a cutoff D degree copies delta hD
  cache_injective := fun i j h => Fin.ext (by
    have := congrArg Fin.val h; rw [cacheW_val, cacheW_val] at this; omega)
  cache_ne_original := fun j h => by
    have hv := congrArg Fin.val h; rw [cacheW_val] at hv; have := T0W_ge mw SV degree
    change _ = 2 at hv; omega
  cache_ne_length := fun j h => by
    have hv := congrArg Fin.val h; rw [cacheW_val] at hv; have := T0W_ge mw SV degree
    change _ = 4 at hv; omega
  cache_ne_flag := fun j h => by
    have hv := congrArg Fin.val h; rw [cacheW_val] at hv; have := T0W_ge mw SV degree
    change _ = 5 at hv; omega
  length_ne_flag := Fin.ne_of_val_ne (by show (4 : ℕ) ≠ 5; decide)
  original_ne_length := Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 4; decide)
  original_ne_flag := Fin.ne_of_val_ne (by show (2 : ℕ) ≠ 5; decide)
  policy_injective := fun i j h => Fin.ext (by
    have := congrArg Fin.val h
    rw [polW_val, polW_val] at this
    have hr := rs_ge a
    have e : NT a (T0W mw SV degree) = T0W mw SV degree + RSt a := rfl
    split_ifs at this <;> omega)
  policy_cache := fun i j h => by
    have := congrArg Fin.val h
    rw [polW_val, cacheW_val] at this
    have hr := rs_ge a
    have e : NT a (T0W mw SV degree) = T0W mw SV degree + RSt a := rfl
    have hj := j.isLt
    split_ifs at this with h0 h42
    · exact Or.inl ⟨h0, Fin.ext (by omega)⟩
    · exact Or.inr ⟨Fin.ext h42, Fin.ext (by show j.val = 13; omega)⟩
    · omega
  policy_core := Fin.ext (by
    rw [polW_val, cacheW_val]
    have h : (W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.coreSlot D).val = 42 := rfl
    rw [h]; rfl)
  policy_ne_original := fun i h => by
    have hv := congrArg Fin.val h; rw [polW_val] at hv; have := T0W_ge mw SV degree
    have e : NT a (T0W mw SV degree) = T0W mw SV degree + RSt a := rfl
    change _ = 2 at hv; split_ifs at hv <;> omega
  policy_ne_length := fun i h => by
    have hv := congrArg Fin.val h; rw [polW_val] at hv; have := T0W_ge mw SV degree
    have e : NT a (T0W mw SV degree) = T0W mw SV degree + RSt a := rfl
    change _ = 4 at hv; split_ifs at hv <;> omega
  policy_ne_flag := fun i h => by
    have hv := congrArg Fin.val h; rw [polW_val] at hv; have := T0W_ge mw SV degree
    have e : NT a (T0W mw SV degree) = T0W mw SV degree + RSt a := rfl
    change _ = 5 at hv; split_ifs at hv <;> omega
  oracleIndex := 3
  two_lt := by decide
  oracle_lt := by
    have := T0W_ge mw SV degree
    have e : NT a (T0W mw SV degree) = T0W mw SV degree + RSt a := rfl
    show 3 < NT a (T0W mw SV degree) + EPt D
    omega
  input_eq := input_eqW mw SV a D degree

end W3.NearCubicWires.RepairSource.Outer3
