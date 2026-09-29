import Proof.Wire_3_5.Recovery.CaseTwoPadGRestrict
import Proof.Wire_3_5.Recovery.CaseTwoPadSource

/-! # The padded source at a guessed width-`q` oracle (P3:3637-3644, 3669-3671, G3)

Realizes "the union machine [...] checks the PCPP of the substituted circuit of the guessed oracle" (P3:3669-3671) for
the verifier padded "to the exact width `q(N)`" (P3:3637-3644), on the raw description of a guessed oracle `O` of the
padded width `q`. From the framed hierarchy word, the raw description of `O`, `1^q` and a unary capacity `1^cap`, one
machine
1. frames the hierarchy word with an empty oracle field (base `CompoundInput`) and runs base's hierarchy stage
   (`PCPPNativeHierarchy.machine`, rewound), which writes the native width `R` as `frame (R.bits)`;
2. blanks the registers of the restriction program to `regTape (cap - 1) 0` (base `RecoveryScratchErase` from
   `1^cap`) and writes its result cell;
3. runs the restriction program (`restrictM`, rewound), which writes `frame (PCPPNative.descriptor (restrictHigh R O))`;
4. frames the hierarchy word with that description (base `CompoundInput`);
5. runs the padded source (`CaseTwoPadSource.omachine`) at the oracle `restrictHigh R O`.
The request it serves is `PCPPRequestBoundary.request a (padSubstituted … O)` (G1), the union setup's padded request
of `O` (`unionRequest_padG`, G2).

Donors checked: base `CompoundInput.pair_ready`, `PCPPNativeHierarchy.raw_run`, `Rewind.reset_run`,
`RecoveryScratchErase.erase_ready`, `ClockJoin.ReadyRun.focus` / `ClockJoin.join`, `TapeEmbedding.run_embed` (used);
C5's `WExec.exec` / `Exec.step` (used); C6's `FrontKit.cell_ready` / `ready_of_step` (same statements, restated here:
not in a verified list).

Paper quantity of the main type (`osourceG_run`): the PCPP clause data of the padded request of a guessed oracle. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.FinalPass.Tm

noncomputable section

/-! ## Generic composition steps -/

/-- A step between zero heads is a ready run. -/
theorem ready_of_step' {t s : ℕ} {p : Machine t s} {n : ℕ} {A A' : Fin t → List Bool}
    (h : ExtDecompositionBatch.Step p n (fun _ => 0) A (fun _ => 0) A') : ClockJoin.ReadyRun p n A A' := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  exact ⟨r, hr, ht, fun i => by rw [hh], hs⟩

/-- A ready run followed by an arbitrary run. -/
theorem ready_then_run {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (input middle : Fin t → List Bool) (hp : ClockJoin.ReadyRun p fp input middle) (s : ExecutionReceipt t b)
    (hq : run q fq middle = some s) :
    ∃ res, run (Composition.machine p q) (fp + 1 + fq) input = some res ∧ res.final.tapes = s.final.tapes ∧
      res.final.heads = s.final.heads ∧ res.steps ≤ fp + 1 + s.steps := by
  obtain ⟨first, hfirst, ht, hh, hs⟩ := hp
  have he : Composition.restart first.final q.start = initialConfiguration q middle := by
    apply configuration_ext
    · rfl
    · funext i; exact hh i
    · exact ht
  have hq' : runFrom q fq (Composition.restart first.final q.start) = some s := by rw [he]; exact hq
  have hr := Composition.run_join p q fp fq _ first s hfirst hq'
  refine ⟨Composition.joinedReceipt first s, hr, rfl, rfl, ?_⟩
  dsimp only [Composition.joinedReceipt]
  omega

/-- A run beside extra tapes. -/
theorem embed_run {t e s : ℕ} (p : Machine t s) (fuel : ℕ) (A : Fin t → List Bool) (E : Fin e → List Bool)
    (r : ExecutionReceipt t s) (h : run p fuel A = some r) :
    run (TapeEmbedding.machine e p) fuel (Fin.addCases A E) = some (TapeEmbedding.receipt (fun _ => 0) E r) := by
  have he := TapeEmbedding.run_embed p (fun _ => 0) E fuel _ r h
  have hi : TapeEmbedding.config (fun _ => 0) E (initialConfiguration p A) =
      initialConfiguration (TapeEmbedding.machine e p) (Fin.addCases A E) := by
    apply configuration_ext
    · rfl
    · funext i
      simp only [TapeEmbedding.config, initialConfiguration]
      exact Fin.addCases (motive := fun j : Fin (t + e) =>
        Fin.addCases (motive := fun _ : Fin (t + e) => ℕ) (fun _ : Fin t => 0) (fun _ : Fin e => 0) j = 0)
        (fun _ => by simp) (fun _ => by simp) i
    · rfl
  rw [hi] at he
  exact he

theorem split_addCases {m n : ℕ} (f : Fin (m + n) → List Bool) :
    f = Fin.addCases (motive := fun _ => List Bool) (fun i => f (i.castAdd n)) (fun j => f (j.natAdd m)) := by
  funext i
  exact Fin.addCases (motive := fun j : Fin (m + n) =>
    f j = Fin.addCases (motive := fun _ => List Bool) (fun i => f (i.castAdd n)) (fun j => f (j.natAdd m)) j)
    (fun _ => by simp) (fun _ => by simp) i

theorem inst_miss {t u : ℕ} {slot : Fin t → Fin u} {A : Fin u → List Bool} {out : Fin t → List Bool} {i : Fin u}
    (h : ∀ j, (slot j).val ≠ i.val) : RecoveryRootRound.install slot A out i = A i :=
  RecoveryRootRound.install_other _ _ _ _ (fun j he => h j (congrArg Fin.val he))

theorem inst_hit {t u : ℕ} {slot : Fin t → Fin u} (hs : Function.Injective slot) {A : Fin u → List Bool}
    {out : Fin t → List Bool} (j : Fin t) {i : Fin u} (h : (slot j).val = i.val) :
    RecoveryRootRound.install slot A out i = out j := by
  rw [← Fin.ext h]
  exact RecoveryRootRound.install_slot _ hs _ _ _

/-! ## The stages -/

/-- One write of `[false]` on a blank tape. -/
def cellM := (Prog.act (fun _ : Fin 1 => some false) (fun _ => .stay) : Prog 1).compile

theorem cell_run : ClockJoin.ReadyRun cellM 1 (fun _ => []) (fun _ => [false]) := by
  have hs := Exec.step (Exec.act (⟨fun _ => 0, fun _ => []⟩ : Bank 1) (fun _ : Fin 1 => some false)
    (fun _ => .stay))
  have hH : ((⟨fun _ => 0, fun _ => []⟩ : Bank 1).act (fun _ : Fin 1 => some false) (fun _ => .stay)).H =
      fun _ => 0 := by funext i; simp [Bank.act, HeadMove.apply]
  have hA : ((⟨fun _ => 0, fun _ => []⟩ : Bank 1).act (fun _ : Fin 1 => some false) (fun _ => .stay)).A =
      fun _ => [false] := by funext i; simp [Bank.act, writeTapeBit]
  rw [hH, hA] at hs
  exact ready_of_step' hs

/-- The restriction program's entry state: `frame (R.bits)`, the raw description, an empty output. -/
def σ0 {q : ℕ} (R : ℕ) (O : BooleanCircuit q) : WState 2 18 :=
  ⟨fun _ => 0, ![RepairOrdinary.frame R.bits, PCPPNative.descriptor O, []], fun _ => 0, false⟩

/-- The rewound restriction machine. -/
def wmM := Rewind.machine (restrictM.toProg.compile)

theorem wenc_H0 (capW : ℕ) {q : ℕ} (R : ℕ) (O : BooleanCircuit q) : (wenc capW (σ0 R O)).H = fun _ => 0 := by
  funext j; simp only [wenc]; split <;> rfl

theorem wenc_σ0 (capW : ℕ) {q : ℕ} (R : ℕ) (O : BooleanCircuit q) (j : Fin (2 + 2 + 18)) :
    (wenc capW (σ0 R O)).A j = if j.val = 0 then RepairOrdinary.frame R.bits else if j.val = 1 then [false]
      else if j.val = 2 then PCPPNative.descriptor O else if j.val = 3 then [] else regTape capW 0 := by
  fin_cases j <;> rfl

theorem regTape_zero (c : ℕ) (hc : 1 ≤ c) : regTape (c - 1) 0 = List.replicate c false := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  simp [regTape, List.replicate_succ]

/-- **The restriction stage**: from the encoded entry bank, the rewound program ends with every head at `0`; the
output stream holds `frame (descriptor (restrictHigh R O))`. -/
theorem wm_run (capW R q : ℕ) (hRq : R ≤ q) (O : BooleanCircuit q) (hcap : 64 * (O.size + q + 4) ≤ capW) :
    ∃ out : Fin (2 + 2 + 18 + 1) → List Bool,
      ClockJoin.ReadyRun wmM (6000 * (capW + 12) ^ 3 + 2) (Fin.addCases (wenc capW (σ0 R O)).A (fun _ => [])) out ∧
      out ⟨3, by omega⟩ = RepairOrdinary.frame (PCPPNative.descriptor (restrictHigh R O)) := by
  obtain ⟨τ, n, hw, hn, -, -, hτO, -, -⟩ := restrictM_spec capW R q hRq O (σ0 R O) rfl rfl rfl
    (fun _ => rfl) (fun _ => rfl) hcap
  have hs := (WExec.exec capW hw).step
  rw [wenc_H0] at hs
  obtain ⟨r, hr, -, ht, hsteps⟩ := hs
  obtain ⟨r', hr', ht', hh', hs', -⟩ := Rewind.reset_run restrictM.toProg.compile n (wenc capW (σ0 R O)).A r hr
  refine ⟨r'.final.tapes, ClockJoin.enlarge _ _ _ _ _ ⟨r', hr', rfl, hh', le_of_eq hs'⟩ (by omega), ?_⟩
  have e : ((sTape (ns := 2) (nr := 18) sO).castAdd 1 : Fin (2 + 2 + 18 + 1)) = ⟨3, by omega⟩ := rfl
  rw [← e, ht', ht, wenc_A_s]
  exact hτO

/-! ## The layout -/

section Layout
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-- The tapes added beside the padded source. -/
def xtapes (k : ℕ) := PCPPNativeHierarchy.tapes source k + 33
abbrev gtapes (a : PointwisePCPPAlgorithm) (k : ℕ) := CaseTwoPadSource.otapes source a k + xtapes source k

/-- The hierarchy stage's width tape. -/
def widx (k : ℕ) : Fin (PCPPNativeHierarchy.tapes source k + 1) :=
  (PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.old source k (HierarchyStreams.bitsR source k))).castAdd 1

theorem gw_lt (a : PointwisePCPPAlgorithm) (k : ℕ) : 438 ≤ PCPPNativeHierarchyNodes.tapes source k ∧
    PCPPNativeHierarchyNodes.tapes source k < CaseTwoPadSource.otapes source a k := by
  have ht : 438 ≤ PCPPNativeHierarchyNodes.tapes source k := by unfold PCPPNativeHierarchyNodes.tapes; omega
  refine ⟨ht, ?_⟩
  simp only [CaseTwoPadSource.otapes, NativeSourceDock.tapes, CaseTwoPadSource.ptapes, CaseTwoPadSource.pbase,
    PCPPNativeClauseDescriptorConsumer.tapes]
  omega

/-! Added tapes (offsets past the block): `0` framed hierarchy word, `1` raw oracle description, `2` `1^cap`,
`3` empty-oracle frame cell, `4-6` first framing scratch, `7` result cell, `8` restricted description,
`9-26` registers, `27` rewind tape, `28` erase tape, `29-31` second framing scratch, `32-` hierarchy stage. -/

def sl1 (a : PointwisePCPPAlgorithm) (k : ℕ) (_ : Fin 1) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 3, by simp only [gtapes, xtapes]; omega⟩
def sl2 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin 6) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k +
      (if j.val = 0 then 0 else if j.val = 1 then 3 else if j.val = 2 then 32 else j.val + 1),
    by have := j.isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩
def sl3 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (PCPPNativeHierarchy.tapes source k + 1)) :
    Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 32 + j.val, by have := j.isLt; simp only [gtapes, xtapes]; omega⟩
def sl4 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (18 + 1 + 1)) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + (if j.val < 18 then 9 + j.val else if j.val = 18 then 2 else 28),
    by have := j.isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩
def sl5 (a : PointwisePCPPAlgorithm) (k : ℕ) (_ : Fin 1) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 7, by simp only [gtapes, xtapes]; omega⟩
def sl6 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (2 + 2 + 18 + 1)) : Fin (gtapes source a k) :=
  ⟨if j.val = 0 then CaseTwoPadSource.otapes source a k + 32 + (widx source k).val
    else CaseTwoPadSource.otapes source a k + (if j.val = 1 then 7 else if j.val = 2 then 1 else if j.val = 3 then 8
      else if j.val < 22 then j.val + 5 else 27),
    by have := j.isLt; have := (widx source k).isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩
def sl7 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin 6) : Fin (gtapes source a k) :=
  ⟨if j.val = 2 then 0 else CaseTwoPadSource.otapes source a k +
      (if j.val = 0 then 0 else if j.val = 1 then 8 else j.val + 26),
    by have := j.isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩

theorem sl1_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl1 source a k) :=
  fun i j _ => Subsingleton.elim i j
theorem sl5_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl5 source a k) :=
  fun i j _ => Subsingleton.elim i j
theorem sl2_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl2 source a k) := by
  intro i j h
  have hv := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  simp only [sl2] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem sl3_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl3 source a k) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [sl3] at hv
  exact Fin.ext (by omega)
theorem sl4_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl4 source a k) := by
  intro i j h
  have hv := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  simp only [sl4] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem sl6_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl6 source a k) := by
  intro i j h
  have hv := congrArg Fin.val h
  have := i.isLt; have := j.isLt; have := (widx source k).isLt
  simp only [sl6] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem sl7_inj (a : PointwisePCPPAlgorithm) (k : ℕ) : Function.Injective (sl7 source a k) := by
  intro i j h
  have hv := congrArg Fin.val h
  have := i.isLt; have := j.isLt; have := (gw_lt source a k).2
  simp only [sl7] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-! ## The machine -/

def stg1 (a : PointwisePCPPAlgorithm) (k : ℕ) := RecoveryFocus.machine (sl1 source a k) cellM
def stg2 (a : PointwisePCPPAlgorithm) (k : ℕ) := RecoveryFocus.machine (sl2 source a k) CompoundInput.machine
def stg3 (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (sl3 source a k) (Rewind.machine (PCPPNativeHierarchy.machine source k CH Cpad code))
def stg4 (a : PointwisePCPPAlgorithm) (k : ℕ) :=
  RecoveryFocus.machine (sl4 source a k) (RecoveryScratchErase.resetMachine 18)
def stg5 (a : PointwisePCPPAlgorithm) (k : ℕ) := RecoveryFocus.machine (sl5 source a k) cellM
def stg6 (a : PointwisePCPPAlgorithm) (k : ℕ) := RecoveryFocus.machine (sl6 source a k) wmM
def stg7 (a : PointwisePCPPAlgorithm) (k : ℕ) := RecoveryFocus.machine (sl7 source a k) CompoundInput.machine

/-- The stages before the padded source. -/
def prefixG (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (stg1 source a k) (stg2 source a k)) (stg3 source a k CH Cpad code)) (stg4 source a k))
    (stg5 source a k)) (stg6 source a k)) (stg7 source a k)

/-- **The padded source at a guessed width-`q` oracle.** -/
def omachineG (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (prefixG source a k CH Cpad code)
    (TapeEmbedding.machine (xtapes source k) (CaseTwoPadSource.omachine source a k CH Cpad code))

/-- Its input: `1^q` on the width tape (index `PCPPNativeHierarchyNodes.tapes source k`), and on the added tapes
`0`, `1`, `2` (indices `otapes`, `otapes + 1`, `otapes + 2`) the framed hierarchy word, the raw oracle description
and `1^cap`; every other tape is blank. -/
def oinputG (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy desc : List Bool) (q cap : ℕ) :
    Fin (gtapes source a k) → List Bool := fun i =>
  if i.val = PCPPNativeHierarchyNodes.tapes source k then List.replicate q true
  else if i.val = CaseTwoPadSource.otapes source a k then RepairOrdinary.frame hierarchy
  else if i.val = CaseTwoPadSource.otapes source a k + 1 then desc
  else if i.val = CaseTwoPadSource.otapes source a k + 2 then List.replicate cap true else []

theorem oinputG_blank (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy desc : List Bool) (q cap : ℕ)
    (i : Fin (gtapes source a k)) (h1 : i.val ≠ PCPPNativeHierarchyNodes.tapes source k)
    (h2 : i.val ≠ CaseTwoPadSource.otapes source a k) (h3 : i.val ≠ CaseTwoPadSource.otapes source a k + 1)
    (h4 : i.val ≠ CaseTwoPadSource.otapes source a k + 2) : oinputG source a k hierarchy desc q cap i = [] := by
  simp [oinputG, h1, h2, h3, h4]

/-- The entry tapes: `1^q` (the width tape), the framed hierarchy word, the raw oracle description, `1^cap`. -/
def gWidth (a : PointwisePCPPAlgorithm) (k : ℕ) : Fin (gtapes source a k) :=
  ⟨PCPPNativeHierarchyNodes.tapes source k, by have := (gw_lt source a k).2; simp only [gtapes, xtapes]; omega⟩
def gHier (a : PointwisePCPPAlgorithm) (k : ℕ) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k, by simp only [gtapes, xtapes]; omega⟩
def gDesc (a : PointwisePCPPAlgorithm) (k : ℕ) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 1, by simp only [gtapes, xtapes]; omega⟩
def gCap (a : PointwisePCPPAlgorithm) (k : ℕ) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 2, by simp only [gtapes, xtapes]; omega⟩

/-- **The entry by tapes.** -/
theorem oinputG_val (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy desc : List Bool) (q cap : ℕ)
    (i : Fin (gtapes source a k)) :
    oinputG source a k hierarchy desc q cap i =
      if i = gWidth source a k then List.replicate q true
      else if i = gHier source a k then RepairOrdinary.frame hierarchy
      else if i = gDesc source a k then desc
      else if i = gCap source a k then List.replicate cap true else [] := by
  simp only [oinputG, gWidth, gHier, gDesc, gCap, Fin.ext_iff]

theorem oinputG_low (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy desc : List Bool) (q cap : ℕ)
    (i : Fin (CaseTwoPadSource.otapes source a k)) :
    oinputG source a k hierarchy desc q cap (Fin.castAdd (xtapes source k) i) =
      if i.val = PCPPNativeHierarchyNodes.tapes source k then List.replicate q true else [] := by
  have gw := gw_lt source a k
  have := i.isLt
  by_cases h : i.val = PCPPNativeHierarchyNodes.tapes source k
  · rw [if_pos h]
    show (if (Fin.castAdd (xtapes source k) i).val = PCPPNativeHierarchyNodes.tapes source k then _ else _) = _
    rw [if_pos (by rw [Fin.val_castAdd]; exact h)]
  · rw [if_neg h]
    apply oinputG_blank <;> rw [Fin.val_castAdd] <;> omega

/-- The output tapes, in the joint layout. -/
def oslotsG (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (RequestSource.tapes a)) : Fin (gtapes source a k) :=
  (CaseTwoPadSource.oslots source a k j).castAdd (xtapes source k)

/-- The stages' budget. -/
def pbudgetG {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (r : InputRequest) (desc' : List Bool) (cap : ℕ) :=
  1 + 1 + CompoundInput.budget (HierarchySourceInput.hierarchyInput H r) [] + 1 +
    (2 * PCPPNativeHierarchy.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
      (List.ofFn r.2) (H.time r.1).bits [] + 2) + 1 + (2 * cap + 4) + 1 + 1 + 1 + (6000 * (cap + 12) ^ 3 + 2) + 1 +
    CompoundInput.budget (HierarchySourceInput.hierarchyInput H r) desc'

/-- **The budget.** -/
def obudgetG (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (hpad : k + 3 ≤ Cpad) (r : InputRequest) {q : ℕ}
    (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (O : BooleanCircuit q) (cap : ℕ) :=
  pbudgetG source H Cpad r (PCPPNative.descriptor (restrictHigh
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)) cap +
    1 + CaseTwoPadSource.obudget source a H Cpad hpad r (restrictHigh
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O) q hq

/-! ## The ambient tapes after each stage -/

/-- Closes a tape-index (in)equality of the layout. -/
local macro "vtac" : tactic => `(tactic| ((try simp only [sl1, sl2, sl3, sl4, sl5, sl6, sl7, Fin.val_mk,
  Fin.val_castAdd, ↓reduceIte, ite_true, ite_false, Nat.reduceEqDiff]) <;> (try split_ifs) <;>
  first | omega | contradiction))
/-- Passes an ambient tape through a stage that does not touch it. -/
local macro "down " h:ident : tactic => `(tactic| (rw [$h:ident, inst_miss] <;>
  first | (intro j'; have := j'.isLt; vtac) | skip))
/-- Reads an ambient tape written by a stage. -/
local macro "hitst " h:ident ", " s:term ", " j:term : tactic => `(tactic| (rw [$h:ident, inst_hit $s $j] <;>
  first | vtac | skip))

section Ambient
variable (a : PointwisePCPPAlgorithm) (k : ℕ) (hier desc : List Bool) (q cap : ℕ)

/-- The erase stage's output: blank registers `replicate cap false`, the kept `1^cap`, its extra tape. -/
def eraseOut : Fin (18 + 1 + 1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin 18 => List.replicate cap false) (fun _ : Fin 1 => List.replicate cap true))
    (fun _ : Fin 1 => List.replicate (max 0 (cap + 1)) false)

def amb1 : Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl1 source a k) (oinputG source a k hier desc q cap) (fun _ => [false])
def amb2 (o2 : Fin 6 → List Bool) : Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl2 source a k) (amb1 source a k hier desc q cap) o2
def amb3 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) :
    Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl3 source a k) (amb2 source a k hier desc q cap o2) t3
def amb4 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) :
    Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl4 source a k) (amb3 source a k hier desc q cap o2 t3) (eraseOut cap)
def amb5 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) :
    Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl5 source a k) (amb4 source a k hier desc q cap o2 t3) (fun _ => [false])
def amb6 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool)
    (o6 : Fin (2 + 2 + 18 + 1) → List Bool) : Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl6 source a k) (amb5 source a k hier desc q cap o2 t3) o6
def amb7 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool)
    (o6 : Fin (2 + 2 + 18 + 1) → List Bool) (o7 : Fin 6 → List Bool) : Fin (gtapes source a k) → List Bool :=
  RecoveryRootRound.install (sl7 source a k) (amb6 source a k hier desc q cap o2 t3 o6) o7

theorem in1 : ∀ j, oinputG source a k hier desc q cap (sl1 source a k j) = (fun _ => ([] : List Bool)) j := by
  have gw := gw_lt source a k
  intro j
  rw [oinputG_blank] <;> first | vtac | rfl

theorem in2 : ∀ j, amb1 source a k hier desc q cap (sl2 source a k j) = CompoundInput.input hier [] j := by
  have gw := gw_lt source a k
  intro j
  obtain ⟨jv, hj⟩ := j
  interval_cases jv
  · down amb1
    simp only [oinputG, sl2, Fin.val_mk]; split_ifs <;> first | rfl | omega
  · hitst amb1, (sl1_inj source a k), 0
    rfl
  all_goals (down amb1; rw [oinputG_blank] <;> first | vtac | rfl)

theorem in3 (o2 : Fin 6 → List Bool) (h22 : o2 2 = RepairOrdinary.frame hier ++ RepairOrdinary.frame []) :
    ∀ j, amb2 source a k hier desc q cap o2 (sl3 source a k j) =
      Fin.addCases (PCPPNativeHierarchy.input source k hier []) (fun _ => []) j := by
  have gw := gw_lt source a k
  have hHT : 4 ≤ PCPPNativeHierarchy.tapes source k := by unfold PCPPNativeHierarchy.tapes; omega
  intro j
  rw [CaseTwoPadSource.addCases_val]
  by_cases hj : j.val = 0
  · hitst amb2, (sl2_inj source a k), ⟨2, by omega⟩
    rw [show o2 ⟨2, by omega⟩ = o2 2 from rfl, h22, dif_pos (by omega)]
    simp [PCPPNativeHierarchy.input, SourceHandoff.sourceTapes, hj, PCPPNativeInputFields.word]
  · down amb2; down amb1
    rw [oinputG_blank] <;> first | vtac | skip
    split_ifs <;> simp [PCPPNativeHierarchy.input, SourceHandoff.sourceTapes, hj]

theorem in4 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) :
    ∀ j, amb3 source a k hier desc q cap o2 t3 (sl4 source a k j) =
      Fin.addCases (Fin.addCases (fun _ : Fin 18 => ([] : List Bool)) (fun _ : Fin 1 => List.replicate cap true))
        (fun _ : Fin 1 => List.replicate 0 false) j := by
  have gw := gw_lt source a k
  intro j
  rw [CaseTwoPadSource.addCases_val]
  split_ifs with h1
  · rw [CaseTwoPadSource.addCases_val]
    split_ifs with h2
    · simp only [Fin.val_mk] at h2
      down amb3; down amb2; down amb1
      rw [oinputG_blank] <;> first | vtac | rfl
    · simp only [Fin.val_mk] at h2
      down amb3; down amb2; down amb1
      simp only [oinputG, sl4, Fin.val_mk]; split_ifs <;> first | rfl | omega
  · down amb3; down amb2; down amb1
    rw [oinputG_blank] <;> first | vtac | rfl

theorem in5 (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) :
    ∀ j, amb4 source a k hier desc q cap o2 t3 (sl5 source a k j) = (fun _ => ([] : List Bool)) j := by
  have gw := gw_lt source a k
  intro j
  down amb4; down amb3; down amb2; down amb1
  rw [oinputG_blank] <;> first | vtac | rfl

theorem in6 (R : ℕ) (O : BooleanCircuit q) (o2 : Fin 6 → List Bool)
    (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool)
    (ht3 : t3 (widx source k) = RepairOrdinary.frame R.bits) (hcap : 1 ≤ cap) :
    ∀ j, amb5 source a k hier (PCPPNative.descriptor O) q cap o2 t3 (sl6 source a k j) =
      Fin.addCases (wenc (cap - 1) (σ0 R O)).A (fun _ => []) j := by
  have gw := gw_lt source a k
  have wl := (widx source k).isLt
  intro j
  rw [CaseTwoPadSource.addCases_val]
  split_ifs with h1
  · rw [wenc_σ0]
    simp only [Fin.val_mk]
    split_ifs with e0 e1 e2 e3
    · down amb5; down amb4
      hitst amb3, (sl3_inj source a k), widx source k
      all_goals exact ht3
    · hitst amb5, (sl5_inj source a k), 0
    · down amb5; down amb4; down amb3; down amb2; down amb1
      simp only [oinputG, sl6, Fin.val_mk]; split_ifs <;> first | rfl | omega
    · down amb5; down amb4; down amb3; down amb2; down amb1
      rw [oinputG_blank] <;> first | vtac | rfl
    · down amb5
      hitst amb4, (sl4_inj source a k), ⟨j.val - 4, by omega⟩
      simp only [eraseOut, CaseTwoPadSource.addCases_val, Fin.val_mk]
      split_ifs <;> first | exact (regTape_zero cap hcap).symm | omega
  · down amb5; down amb4; down amb3; down amb2; down amb1
    rw [oinputG_blank] <;> first | vtac | rfl

theorem in7 (desc' : List Bool) (o2 : Fin 6 → List Bool)
    (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) (o6 : Fin (2 + 2 + 18 + 1) → List Bool)
    (h20 : o2 0 = RepairOrdinary.frame hier) (h63 : o6 ⟨3, by omega⟩ = RepairOrdinary.frame desc') :
    ∀ j, amb6 source a k hier desc q cap o2 t3 o6 (sl7 source a k j) = CompoundInput.input hier desc' j := by
  have gw := gw_lt source a k
  have wl := (widx source k).isLt
  intro j
  obtain ⟨jv, hj⟩ := j
  interval_cases jv
  · down amb6; down amb5; down amb4; down amb3
    hitst amb2, (sl2_inj source a k), ⟨0, by omega⟩
    rw [show o2 ⟨0, by omega⟩ = o2 0 from rfl, h20]; rfl
  · hitst amb6, (sl6_inj source a k), ⟨3, by omega⟩
    rw [h63]; rfl
  all_goals (down amb6; down amb5; down amb4; down amb3; down amb2; down amb1
             rw [oinputG_blank] <;> first | vtac | rfl)

theorem blockM (desc' : List Bool) (o2 : Fin 6 → List Bool)
    (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool) (o6 : Fin (2 + 2 + 18 + 1) → List Bool)
    (o7 : Fin 6 → List Bool) (h72 : o7 2 = RepairOrdinary.frame hier ++ RepairOrdinary.frame desc') :
    (fun i => amb7 source a k hier desc q cap o2 t3 o6 o7 (Fin.castAdd (xtapes source k) i)) =
      CaseTwoPadSource.oinput source a k hier desc' q := by
  have gw := gw_lt source a k
  have wl := (widx source k).isLt
  funext i
  have := i.isLt
  rw [CaseTwoPadSource.oinput_val]
  by_cases h0 : i.val = 0
  · rw [if_pos h0]
    hitst amb7, (sl7_inj source a k), ⟨2, by omega⟩
    rw [show o7 ⟨2, by omega⟩ = o7 2 from rfl, h72]; rfl
  · rw [if_neg h0]
    down amb7; down amb6; down amb5; down amb4; down amb3; down amb2; down amb1
    rw [oinputG_low]

end Ambient

/-! ## The run -/

theorem receipt_tapes {t e s : ℕ} (heads : Fin e → ℕ) (E : Fin e → List Bool) (r : ExecutionReceipt t s)
    (i : Fin t) : (TapeEmbedding.receipt heads E r).final.tapes (Fin.castAdd e i) = r.final.tapes i := by
  simp [TapeEmbedding.receipt, TapeEmbedding.config]

theorem receipt_heads {t e s : ℕ} (heads : Fin e → ℕ) (E : Fin e → List Bool) (r : ExecutionReceipt t s)
    (i : Fin t) : (TapeEmbedding.receipt heads E r).final.heads (Fin.castAdd e i) = r.final.heads i := by
  simp [TapeEmbedding.receipt, TapeEmbedding.config]

/-- **The stages before the source are ready**: they end with the hierarchy word framed with the restricted
description on the input tape. -/
theorem prefix_run (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest) (q : ℕ)
    (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (O : BooleanCircuit q) (cap : ℕ) (hcap : 64 * (O.size + q + 4) + 1 ≤ cap) :
    ∃ (o2 : Fin 6 → List Bool) (t3 : Fin (PCPPNativeHierarchy.tapes source k + 1) → List Bool)
      (o6 : Fin (2 + 2 + 18 + 1) → List Bool) (o7 : Fin 6 → List Bool),
      ClockJoin.ReadyRun (prefixG source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (pbudgetG source H Cpad r (PCPPNative.descriptor (restrictHigh
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)) cap)
        (oinputG source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap)
        (amb7 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2 t3 o6 o7) ∧
      o7 2 = RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r) ++
        RepairOrdinary.frame (PCPPNative.descriptor (restrictHigh
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)) := by
  -- the stages' runs
  obtain ⟨o2, r2, h22, h20, -⟩ := CompoundInput.pair_ready (HierarchySourceInput.hierarchyInput H r) []
  obtain ⟨res3, hrun3, hst3, hF3, -⟩ := PCPPNativeHierarchy.raw_run source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) (List.ofFn r.2) (H.time r.1).bits [] hpad
  obtain ⟨rw3, hrw3, hrwt3, hrwh3, hrws3, -⟩ := Rewind.reset_run _ _ _ res3 hrun3
  have r3 : ClockJoin.ReadyRun (Rewind.machine (PCPPNativeHierarchy.machine source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier))) (2 * PCPPNativeHierarchy.budget source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) (List.ofFn r.2) (H.time r.1).bits [] + 2)
      (Fin.addCases (PCPPNativeHierarchy.input source k (HierarchySourceInput.hierarchyInput H r) [])
        (fun _ => [])) rw3.final.tapes :=
    ClockJoin.enlarge _ _ _ _ _ ⟨rw3, hrw3, rfl, hrwh3, le_of_eq hrws3⟩ (by omega)
  have ht3 : rw3.final.tapes (widx source k) = RepairOrdinary.frame
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2).bits :=
    (hrwt3 _).trans hF3.width
  have r4 : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 18) (2 * cap + 4)
      (Fin.addCases (Fin.addCases (fun _ : Fin 18 => ([] : List Bool)) (fun _ : Fin 1 => List.replicate cap true))
        (fun _ : Fin 1 => List.replicate 0 false)) (eraseOut cap) := by
    obtain ⟨rr, hr, ht, hh, hs⟩ := RecoveryScratchErase.erase_ready (t := 18) cap 0 (fun _ => []) (fun _ => by simp)
    exact ⟨rr, hr, ht, hh, hs.le⟩
  obtain ⟨o6, r6, h63⟩ := wm_run (cap - 1) (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) r.2) q hq O (by omega)
  have r6' := ClockJoin.enlarge _ _ _ _ _ r6 (show 6000 * (cap - 1 + 12) ^ 3 + 2 ≤ 6000 * (cap + 12) ^ 3 + 2 by
    have := Nat.pow_le_pow_left (show cap - 1 + 12 ≤ cap + 12 by omega) 3
    omega)
  obtain ⟨o7, r7, h72, -, -⟩ := CompoundInput.pair_ready (HierarchySourceInput.hierarchyInput H r)
    (PCPPNative.descriptor (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2) O))
  -- the stages, focused
  have g1 := ClockJoin.ReadyRun.focus cell_run (sl1 source a k) (sl1_inj source a k) _
    (in1 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap)
  have g2 := ClockJoin.ReadyRun.focus r2 (sl2 source a k) (sl2_inj source a k) _
    (in2 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap)
  have g3 := ClockJoin.ReadyRun.focus r3 (sl3 source a k) (sl3_inj source a k) _
    (in3 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2 h22)
  have g4 := ClockJoin.ReadyRun.focus r4 (sl4 source a k) (sl4_inj source a k) _
    (in4 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2 rw3.final.tapes)
  have g5 := ClockJoin.ReadyRun.focus cell_run (sl5 source a k) (sl5_inj source a k) _
    (in5 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2 rw3.final.tapes)
  have g6 := ClockJoin.ReadyRun.focus r6' (sl6 source a k) (sl6_inj source a k) _
    (in6 source a k (HierarchySourceInput.hierarchyInput H r) q cap _ O o2 rw3.final.tapes ht3 (by omega))
  have g7 := ClockJoin.ReadyRun.focus r7 (sl7 source a k) (sl7_inj source a k) _
    (in7 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap _ o2
      rw3.final.tapes o6 h20 h63)
  have j2 := ClockJoin.join _ _ _ _ _ _ _ g1 g2
  have j3 := ClockJoin.join _ _ _ _ _ _ _ j2 g3
  have j4 := ClockJoin.join _ _ _ _ _ _ _ j3 g4
  have j5 := ClockJoin.join _ _ _ _ _ _ _ j4 g5
  have j6 := ClockJoin.join _ _ _ _ _ _ _ j5 g6
  have j7 := ClockJoin.join _ _ _ _ _ _ _ j6 g7
  exact ⟨o2, rw3.final.tapes, o6, o7, j7, h72⟩

/-- **The padded source at a guessed width-`q` oracle is ready**: from the framed hierarchy word, the raw description
of `O`, `1^q` and `1^cap`, the clause data of the PCPP output of the padded request of `O`
(`PCPPRequestBoundary.request a (padSubstituted … O)`) and its framed input, on the output tapes. -/
theorem osourceG_run (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest) (q : ℕ)
    (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (O : BooleanCircuit q) (cap : ℕ) (hcap : 64 * (O.size + q + 4) + 1 ≤ cap) :
    let request := PCPPRequestBoundary.request a
      (padSubstituted source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad hq O)
    ∃ result, run (omachineG source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (obudgetG source a H Cpad hpad r hq O cap)
      (oinputG source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap) = some result ∧
      result.steps ≤ obudgetG source a H Cpad hpad r hq O cap ∧
      (∀ j, result.final.tapes (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))) =
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size + request.arity)) [] j) ∧
      (∀ j, result.final.heads (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))) =
        PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a))) =
        RepairOrdinary.frame (pcppInput request) ∧
      result.final.heads (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a))) = 0 := by
  intro request
  obtain ⟨o2, t3, o6, o7, pre, h72⟩ := prefix_run source a H Cpad hpad r q hq O cap hcap
  -- the padded source at the restricted oracle
  obtain ⟨s, hs, hsteps, hdata, hheads, hreq, hreqh⟩ := CaseTwoPadSource.osource_run source a H Cpad hcoeff hpad r
    (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
      O) q hq
  have he := embed_run (CaseTwoPadSource.omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    _ _ (fun j => amb7 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2
      t3 o6 o7 (Fin.natAdd (CaseTwoPadSource.otapes source a k) j)) s hs
  have he' : run (TapeEmbedding.machine (xtapes source k)
      (CaseTwoPadSource.omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)))
      (CaseTwoPadSource.obudget source a H Cpad hpad r (restrictHigh
        (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O) q hq)
      (amb7 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2
        t3 o6 o7) =
      some (TapeEmbedding.receipt (fun _ => 0) (fun j => amb7 source a k (HierarchySourceInput.hierarchyInput H r)
        (PCPPNative.descriptor O) q cap o2 t3 o6 o7 (Fin.natAdd (CaseTwoPadSource.otapes source a k) j))
        s) := by
    have e : amb7 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2
        t3 o6 o7 = Fin.addCases (motive := fun _ => List Bool) (CaseTwoPadSource.oinput source a k
          (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor (restrictHigh
            (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)) q)
          (fun j => amb7 source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap o2
            t3 o6 o7 (Fin.natAdd (CaseTwoPadSource.otapes source a k) j)) := by
      rw [← blockM source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor O) q cap _ o2
        t3 o6 o7 h72]
      exact split_addCases _
    exact (congrArg (fun A => run (TapeEmbedding.machine (xtapes source k)
      (CaseTwoPadSource.omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)))
      (CaseTwoPadSource.obudget source a H Cpad hpad r (restrictHigh
        (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O) q hq)
      A) e).trans he
  obtain ⟨res, hres, hrt, hrh, hrs⟩ := ready_then_run _ _ _ _ _ _ pre _ he'
  have hse : (TapeEmbedding.receipt (fun _ => 0) (fun j => amb7 source a k (HierarchySourceInput.hierarchyInput H r)
    (PCPPNative.descriptor O) q cap o2 t3 o6 o7 (Fin.natAdd (CaseTwoPadSource.otapes source a k) j))
    s).steps = s.steps := rfl
  have eT : ∀ i : Fin (CaseTwoPadSource.otapes source a k),
      res.final.tapes (Fin.castAdd (xtapes source k) i) = s.final.tapes i := fun i =>
    (congrFun hrt _).trans (receipt_tapes _ _ s i)
  have eH : ∀ i : Fin (CaseTwoPadSource.otapes source a k),
      res.final.heads (Fin.castAdd (xtapes source k) i) = s.final.heads i := fun i =>
    (congrFun hrh _).trans (receipt_heads _ _ s i)
  refine ⟨res, hres, ?_, fun j => (eT _).trans (hdata j), fun j => (eH _).trans (hheads j), (eT _).trans hreq,
    (eH _).trans hreqh⟩
  unfold obudgetG
  omega

end Layout

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
