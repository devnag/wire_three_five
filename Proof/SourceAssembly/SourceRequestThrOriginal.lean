import Proof.SourceAssembly.SourceRequestThrOriginalForward
import Proof.SourceAssembly.SourceRequestThrKinds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.ThrOriginal
open PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] CloseoutRowsSupportStream.Threshold.machine CloseoutRowsSupportStream.Threshold.program

/-! ## The writer and its two framed chains -/

/-- The original THR writer from zero heads: one move puts head 1674 at 1 (the writer's start heads). -/
def writer := Composition.machine (CompetitorCountTable.moveMachine (1674 : Fin 1704))
  CloseoutRowsSupportStream.Threshold.machine

theorem writer_native_forward : CursorRestore.NoLeft writer (1688 : Fin 1704) :=
  CursorRestore.composition_forward _ _ _ (ThrOriginalForward.move_forward _ _)
    ThrOriginalForward.native_forward

/-- The retained-bottom support stream of `c` (the writer's tape 1703). -/
def stream {q : Nat} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  CloseoutRowsSupportStream.supportWord (List.ofFn (fun i => c.bottom (retainedTopIndex c i)))

/-- The writer's input words (`Threshold.input P q W L bits [] []`). -/
abbrev input (P q W L : Nat) (bits : List Bool) : Fin 1704 → List Bool :=
  CloseoutRowsSupportStream.Threshold.input P q W L bits [] []

theorem heads_native (n s : List Bool) :
    CloseoutRowsSupportStream.Threshold.heads n s (1688 : Fin 1704) = n.length := by
  change Fin.addCases (m := 1703) (n := 1) (motive := fun _ => Nat)
    (CloseoutRowsCircuitColdEntry.heads n) (fun _ => s.length) (Fin.castAdd 1 (1688 : Fin 1703)) = _
  rw [Fin.addCases_left]
  simp [CloseoutRowsCircuitColdEntry.heads]

theorem heads_support (n s : List Bool) :
    CloseoutRowsSupportStream.Threshold.heads n s (1703 : Fin 1704) = s.length := by
  change Fin.addCases (m := 1703) (n := 1) (motive := fun _ => Nat)
    (CloseoutRowsCircuitColdEntry.heads n) (fun _ => s.length) (Fin.natAdd 1703 (0 : Fin 1)) = _
  rw [Fin.addCases_right]

/-- One move of `target`, then `M`, at a SYMBOLIC machine `M` (so no concrete rule table is ever unfolded). -/
theorem move_then {t s : Nat} (target : Fin t) (M : Machine t s) (fuel : Nat) (a : Fin t → List Bool)
    (f : ExecutionReceipt t s)
    (hf : runFrom M fuel ⟨M.start, fun i => if i = target then 1 else 0, a⟩ = some f) :
    ∃ r : ExecutionReceipt t (2 + s),
      run (Composition.machine (CompetitorCountTable.moveMachine target) M) (1 + 1 + fuel) a = some r ∧
      r.steps = 1 + 1 + f.steps ∧ r.final.heads = f.final.heads ∧ r.final.tapes = f.final.tapes := by
  obtain ⟨m, hm, mh, mt, ms⟩ := CompetitorCountTable.move_run target (fun _ => 0) a
  have hre : Composition.restart m.final M.start = ⟨M.start, fun i => if i = target then 1 else 0, a⟩ := by
    apply configuration_ext
    · rfl
    · change m.final.heads = _
      rw [mh]
    · change m.final.tapes = _
      rw [mt]
  have hj := Composition.run_join _ _ 1 _ _ m f hm (by rw [hre]; exact hf)
  refine ⟨Composition.joinedReceipt m f, hj, ?_, rfl, rfl⟩
  change m.steps + 1 + f.steps = _
  rw [ms]

theorem start_heads :
    CloseoutRowsSupportStream.Threshold.heads [] [] = fun i : Fin 1704 => if i = 1674 then 1 else 0 := by
  funext i
  rw [PCJ6e421fabe2aa4155_SourceCircuitNative.empty_heads]
  by_cases h : i = 1674
  · rw [if_pos h, if_pos (show i.val = 1674 from congrArg Fin.val h)]
  · rw [if_neg h, if_neg (show ¬ i.val = 1674 from fun e => h (Fin.ext e))]

/-- **The writer's raw run** (no rewind): the bare native word and the support stream, each with its
head at its length. -/
theorem writer_run {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ source : ExecutionReceipt 1704 (2 + CloseoutRowsSupportStream.Threshold.program.1),
      run writer (1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length)
        (input P q W L bits) = some source ∧
      source.steps ≤ 1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length ∧
      source.final.tapes 1688 = thrWord c ∧ source.final.heads 1688 = (thrWord c).length ∧
      source.final.tapes 1703 = stream c ∧ source.final.heads 1703 = (stream c).length := by
  obtain ⟨typed, native⟩ := CloseoutRowsCircuitMeaning.threshold_typed c W L bits hd
  have hp := typed.mpr ⟨hW, hL⟩
  obtain ⟨f, hf, hfs, _fh, _flag, _rh, _raw, _dh, _drv, good⟩ :=
    CloseoutRowsSupportStream.Threshold.cold_run P q W L bits [] [] hcap
  obtain ⟨heads, word, _arity, _driver, _W, _L, _raw', support, _bound⟩ := good hp
  rw [start_heads] at hf
  obtain ⟨r, hr, rs, rh, rt⟩ := move_then (1674 : Fin 1704) CloseoutRowsSupportStream.Threshold.machine _ _ f hf
  have hsup := CloseoutRowsSupportStream.Threshold.support_typed c bits hd
  refine ⟨r, hr, by omega, ?_, ?_, ?_, ?_⟩
  · rw [rt, word, List.nil_append, native]
    rfl
  · rw [rh, heads, heads_native, List.nil_append, native]
    rfl
  · rw [rt, support, List.nil_append, hsup]
    rfl
  · rw [rh, heads, heads_support, List.nil_append, hsup]
    rfl

/-- The writer's fuel bound. -/
def wFuel (P q : Nat) (bits : List Bool) : Nat :=
  1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length

def chainA := AppendOutputFrame.machine writer (1688 : Fin 1704)

/-- **Chain A**: `frame (thrWord c)` on 1706 and the bare `thrWord c` kept on 1688; every head `0`. -/
theorem chainA_run {q : Nat} (c : NormalizedThresholdThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedThresholdThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ A, Step chainA (2 * wFuel P q bits + 4 * (thrWord c).length + 7) (fun _ => 0)
        (AppendOutputFrame.input (input P q W L bits)) (fun _ => 0) A ∧
      A 1706 = frame (thrWord c) ∧ A 1688 = thrWord c := by
  obtain ⟨source, hr, hs, t88, h88, -, -⟩ := writer_run c P W L bits hcap hd hW hL
  obtain ⟨s, sr, st, sh, sk, ss⟩ := PCPPNativeFrame.frame_run writer 1688 writer_native_forward
    _ _ source hr (thrWord c) t88 h88
  refine ⟨s.final.tapes, (Step.of_run sr (funext sh) rfl).enlarge (by unfold wFuel; omega), st, ?_⟩
  exact (sk 1688).trans t88

/-! ## The writer's entry bank, tape by tape -/

/-- The writer's input word at tape number `n` (`CloseoutRowsCircuit.input` with empty streams). -/
def thrAt (P q W L : Nat) (bits : List Bool) (n : Nat) : List Bool :=
  if n = 1 then frame bits else if n = 1674 then UnaryTemplate.tape q else
    if n = 1694 then List.replicate P true else
      if n = 1698 then List.replicate W true else if n = 1699 then List.replicate L true else []

theorem thrAt_nil (P q W L : Nat) (bits : List Bool) (n : Nat) (h1 : n ≠ 1) (h2 : n ≠ 1674)
    (h3 : n ≠ 1694) (h4 : n ≠ 1698) (h5 : n ≠ 1699) : thrAt P q W L bits n = [] := by
  unfold thrAt
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

theorem thrAt_high (P q W L : Nat) (bits : List Bool) (n : Nat) (h : 1700 ≤ n) :
    thrAt P q W L bits n = [] :=
  thrAt_nil P q W L bits n (by omega) (by omega) (by omega) (by omega) (by omega)

theorem stepAt {m n : Nat} (g : Nat → List Bool) (hg : ∀ k, m ≤ k → g k = []) (f : Fin m → List Bool)
    (hf : ∀ j : Fin m, f j = g j.val) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin n => []) i = g i.val := by
  rw [Gen.ChainIn.addCases_nil]
  by_cases h : i.val < m
  · rw [dif_pos h, hf]
  · rw [dif_neg h, hg _ (by omega)]

theorem cold_at (P q W L : Nat) (bits : List Bool) (j : Fin 1703) :
    CloseoutRowsCircuitColdEntry.input P q W L bits [] j = thrAt P q W L bits j.val := by
  unfold CloseoutRowsCircuitColdEntry.input
  by_cases h : j = 1688
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    rfl

theorem input_at0 (P q W L : Nat) (bits : List Bool) (j : Fin 1704) :
    input P q W L bits j = thrAt P q W L bits j.val :=
  stepAt (n := 1) _ (fun k hk => thrAt_high P q W L bits k (by omega)) _ (cold_at P q W L bits) j

/-- **The chains' entry**, tape by tape. -/
theorem input_at (P q W L : Nat) (bits : List Bool) (i : Fin 1708) :
    AppendOutputFrame.input (input P q W L bits) i = thrAt P q W L bits i.val := by
  have hg : ∀ m, 1700 ≤ m → ∀ k, m ≤ k → thrAt P q W L bits k = [] :=
    fun m hm k hk => thrAt_high P q W L bits k (by omega)
  have l1 : ∀ j : Fin 1705, AppendOutputLength.input (input P q W L bits) j = thrAt P q W L bits j.val :=
    stepAt (n := 1) _ (hg 1704 (by omega)) _ (input_at0 P q W L bits)
  have l2 : ∀ j : Fin 1706, AppendOutputLength.input (AppendOutputLength.input (input P q W L bits)) j
      = thrAt P q W L bits j.val :=
    stepAt (n := 1) _ (hg 1705 (by omega)) _ l1
  exact stepAt (n := 2) _ (hg 1706 (by omega)) _ l2 i

/-! ## The five-stage layout in `Fin (3425 + Tn a)` -/





/-! ### Stage entries -/

/-! ### The machine and its run -/


section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

end normal
end NearCubicWires.SourceRequest.ThrOriginal

