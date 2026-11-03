import Proof.Packets.SrcStartCopyFrames
import Proof.PCP.PCPPQueryNatural
import Proof.MachineModel.GeneratedAmplifierCopy
import Proof.Hierarchy.HierarchyFixedWord
import Proof.Assembly.Production

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Circuit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.CompilerSemantics
noncomputable section

/-! ## The circuit payloads are segments -/

theorem symWord_segment {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    PCJd4d1d9d7d1fa4313_Production.symWord c =
      ExtDecompositionBatch.segment (symmetricCircuitOccurrences c) (List.ofFn c.top) := by
  unfold PCJd4d1d9d7d1fa4313_Production.symWord ExtDecompositionBatch.segment symmetricCircuitOccurrences
  rw [List.length_ofFn]
  rfl

theorem thrWord_segment {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    PCJd4d1d9d7d1fa4313_Production.thrWord c =
      ExtDecompositionBatch.segment (thresholdCircuitOccurrences c)
        (thresholdWord (nonStrictAsStrict (retainedTopGate c))) := by
  unfold PCJd4d1d9d7d1fa4313_Production.thrWord ExtDecompositionBatch.segment thresholdCircuitOccurrences
  rw [List.length_ofFn]
  rfl

/-! ## Fixed-word append at the end of a tape -/

def acfg (l bits : List Bool) (pos : ℕ) (hp : pos ≤ bits.length) : Configuration 1 (bits.length+1) :=
  ⟨⟨pos,by omega⟩,fun _ => l.length+pos,fun _ => l++bits.take pos⟩

theorem append_write (l bits : List Bool) (pos : ℕ) (hp : pos < bits.length) :
    step (HierarchyFixedWord.raw bits) (acfg l bits pos hp.le) = some (acfg l bits (pos+1) (by omega)) := by
  simp [step,HierarchyFixedWord.raw,acfg,hp]
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction,HeadMove.apply]
    omega
  · funext i
    simp only [applyAction]
    have h := Streaming.write_append (l++bits.take pos) bits[pos]
    have hl : (l++bits.take pos).length = l.length+pos := by simp [Nat.min_eq_left hp.le]
    rw [hl] at h
    rw [h,List.append_assoc,List.take_append_getElem hp]

theorem append_prefix (l bits : List Bool) (pos remaining : ℕ) (hp : pos+remaining = bits.length) :
    Timed (HierarchyFixedWord.raw bits) remaining (acfg l bits pos (by omega))
      (acfg l bits bits.length (by omega)) := by
  induction remaining generalizing pos with
  | zero =>
    have he : pos = bits.length := by omega
    subst pos
    exact Timed.refl _ _
  | succ remaining ih =>
    exact Timed.step (by simp [HierarchyFixedWord.raw,acfg]; omega) (append_write l bits pos (by omega))
      (ih (pos+1) (by omega))

/-- **Append a fixed word** at the end of the (single) tape. -/
theorem append_step (l bits : List Bool) :
    Step (HierarchyFixedWord.raw bits) bits.length (fun _ => l.length) (fun _ => l)
      (fun _ => l.length+bits.length) (fun _ => l++bits) := by
  obtain ⟨r,hr,hf,hs⟩ := (append_prefix l bits 0 bits.length (by omega)).run (by simp [HierarchyFixedWord.raw,acfg])
  refine ⟨r,?_,?_,?_,hs.le⟩
  · convert hr using 2
    simp only [acfg,List.take_zero,List.append_nil,Nat.add_zero]
    rfl
  · rw [hf]
    rfl
  · rw [hf]
    funext i
    simp [acfg]

/-! ## The unframer as a `Step` -/

/-- **Unframe**: `frame bits` at the source cursor is appended, unframed, to the output (head at its end). -/
theorem unframe_step (pre bits tail out : List Bool) :
    Step GeneratedAmplifier.Copy.machine (2*bits.length+1) ![pre.length,out.length] ![pre++frame bits++tail,out]
      ![pre.length+2*bits.length+1,(out++bits).length] ![pre++frame bits++tail,out++bits] := by
  obtain ⟨r,hr,hf,hs⟩ := GeneratedAmplifier.Copy.copy_run pre bits tail out
  exact ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs.le⟩

/-! ## One circuit: count, skip the top frame, copy the bottom frames -/

/-- The circuit's bottom words. -/
def bottoms {q : ℕ} (gs : List (SupportedNormalizedGate q)) : List (List Bool) :=
  gs.map CloseoutRowsCircuitBottom.nativeWord

theorem frames_bottoms {q : ℕ} (gs : List (SupportedNormalizedGate q)) :
    CopyFrames.frames (bottoms gs) = gs.flatMap (fun g => frame (CloseoutRowsCircuitBottom.nativeWord g)) := by
  simp [CopyFrames.frames,bottoms,List.flatMap_map]

theorem segment_split {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t : List Bool) :
    ExtDecompositionBatch.segment gs t = natWord gs.length++frame t++CopyFrames.frames (bottoms gs) := by
  rw [frames_bottoms]
  rfl

/-- Local layout (12 tapes): 0 the payload, 1 the stream, 2–11 the count reader's scratch (its port `k` at `k+1`),
11 the count template that drives the copy loop. -/
def capSlots (i : Fin 11) : Fin 12 := if i.val = 0 then 0 else ⟨i.val+1,by omega⟩
def skipSlots : Fin 2 → Fin 12 := ![0,1]
def copySlots : Fin 3 → Fin 12 := ![0,1,11]
theorem cap_injective : Function.Injective capSlots := by decide
theorem skip_injective : Function.Injective skipSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide

def cap := RecoveryFocus.machine capSlots PCPPQueryNatural.machine
def skip := RecoveryFocus.machine skipSlots (frameMachine false)
def copy := RecoveryFocus.machine copySlots CopyFrames.machine
/-- **The circuit machine** (one fixed machine). -/
def circ := Composition.machine (Composition.machine cap skip) copy

def capCost (n : ℕ) : ℕ := PCPPQueryNatural.budget n
def circCost {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t : List Bool) : ℕ :=
  capCost gs.length+1+(2*t.length+1)+1+CopyFrames.copyCost (bottoms gs)

def inHeads (S : List Bool) : Fin 12 → ℕ := fun i => if i.val = 1 then S.length else 0
def inBank (Z S : List Bool) : Fin 12 → List Bool := fun i => if i.val = 0 then Z else if i.val = 1 then S else []

/-- **One circuit's bottom frames onto the stream**: from the payload `segment gs t ++ tail` (head 0), the stream `S` (head
at its end) and blank scratch, append `gs.flatMap (frame ∘ nativeWord)` to `S`; the payload is kept. -/
theorem circ_step {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t tail S : List Bool) :
    ∃ (H : Fin 12 → ℕ) (A : Fin 12 → List Bool),
      Step circ (circCost gs t) (inHeads S) (inBank (ExtDecompositionBatch.segment gs t++tail) S) H A ∧
      A 0 = ExtDecompositionBatch.segment gs t++tail ∧
      A 1 = S++gs.flatMap (fun g => frame (CloseoutRowsCircuitBottom.nativeWord g)) ∧
      H 1 = (S++gs.flatMap (fun g => frame (CloseoutRowsCircuitBottom.nativeWord g))).length := by
  let n := gs.length
  let bs := bottoms gs
  have hbs : bs.length = n := by simp [bs,n,bottoms]
  let src := ExtDecompositionBatch.segment gs t++tail
  have hsrc : src = natWord n++(frame t++CopyFrames.frames bs++tail) := by
    simp only [src,segment_split,List.append_assoc,bs,n]
  -- stage 1: the count
  obtain ⟨rc,hrc,_hsteps,o0,oh0,o10,oh10⟩ :=
    PCPPQueryNatural.natural_run [] (frame t++CopyFrames.frames bs++tail) n
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hrc o0 oh0
  rw [← hsrc] at hrc o0
  have hc : Step PCPPQueryNatural.machine (capCost n) (fun i => if i = 0 then 0 else 0)
      (fun i => if i = 0 then src else []) rc.final.heads rc.final.tapes := Step.of_run hrc rfl rfl
  let Hc := rc.final.heads
  let Ac := rc.final.tapes
  have d1 := hc.dock capSlots cap_injective (inHeads S) (inBank src S)
    (by intro j;fin_cases j <;> simp [capSlots,inHeads])
    (by intro j;fin_cases j <;> simp [capSlots,inBank])
  let H1 := dockH capSlots (inHeads S) Hc
  let A1 := install capSlots (inBank src S) Ac
  have a10 : A1 0 = src := (install_slot capSlots cap_injective _ _ 0).trans o0
  have h10 : H1 0 = 2*natBitLength n+1 := (dockH_slot capSlots cap_injective _ _ 0).trans oh0
  have a11 : A1 1 = S := (install_other capSlots _ _ 1 (by intro j;fin_cases j <;> decide)).trans (by simp [inBank])
  have h11 : H1 1 = S.length := (dockH_other capSlots _ _ 1 (by intro j;fin_cases j <;> decide)).trans (by simp [inHeads])
  have a1d : A1 11 = UnaryTemplate.tape n := (install_slot capSlots cap_injective _ _ 10).trans o10
  have h1d : H1 11 = 1 := (dockH_slot capSlots cap_injective _ _ 10).trans oh10
  -- stage 2: skip the top frame
  have s2 := frame_run false (natWord n) t (CopyFrames.frames bs++tail) S
  simp only [selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at s2
  have hwn : (natWord n).length = 2*natBitLength n+1 := DecompositionSource.natWord_length n
  have d2 := s2.dock skipSlots skip_injective H1 A1
    (by intro j;fin_cases j
        · simp [skipSlots,CloseoutRowsTupleSeek.fieldHeads,h10,hwn]
        · simp [skipSlots,CloseoutRowsTupleSeek.fieldHeads,h11])
    (by intro j;fin_cases j
        · simp [skipSlots,CloseoutRowsTupleSeek.fieldData,a10,hsrc,List.append_assoc]
        · simp [skipSlots,CloseoutRowsTupleSeek.fieldData,a11])
  let H2 := dockH skipSlots H1 (CloseoutRowsTupleSeek.fieldHeads ((natWord n).length+(frame t).length) S)
  let A2 := install skipSlots A1 (CloseoutRowsTupleSeek.fieldData (natWord n++frame t++(CopyFrames.frames bs++tail)) S)
  have h20 : H2 0 = (natWord n++frame t).length :=
    (dockH_slot skipSlots skip_injective H1 _ 0).trans (by simp [CloseoutRowsTupleSeek.fieldHeads])
  have a20 : A2 0 = natWord n++frame t++CopyFrames.frames bs++tail := by
    have h := install_slot skipSlots skip_injective A1 (CloseoutRowsTupleSeek.fieldData (natWord n++frame t++(CopyFrames.frames bs++tail)) S) 0
    simpa [A2,skipSlots,CloseoutRowsTupleSeek.fieldData,List.append_assoc] using h
  have h21 : H2 1 = S.length :=
    (dockH_slot skipSlots skip_injective H1 _ 1).trans (by simp [CloseoutRowsTupleSeek.fieldHeads])
  have a21 : A2 1 = S := by
    have h := install_slot skipSlots skip_injective A1 (CloseoutRowsTupleSeek.fieldData (natWord n++frame t++(CopyFrames.frames bs++tail)) S) 1
    simpa [A2,skipSlots,CloseoutRowsTupleSeek.fieldData] using h
  have h2d : H2 11 = 1 := (dockH_other skipSlots _ _ 11 (by intro j;fin_cases j <;> decide)).trans h1d
  have a2d : A2 11 = UnaryTemplate.tape n := (install_other skipSlots _ _ 11 (by intro j;fin_cases j <;> decide)).trans a1d
  -- stage 3: copy the bottom frames
  have s3 := CopyFrames.copy_step bs (natWord n++frame t) tail S
  rw [hbs] at s3
  have d3 := s3.dock copySlots copy_injective H2 A2
    (by intro j;fin_cases j
        · simpa [copySlots,CopyFrames.heads] using h20
        · simpa [copySlots,CopyFrames.heads] using h21
        · simpa [copySlots,CopyFrames.heads] using h2d)
    (by intro j;fin_cases j
        · simpa [copySlots,CopyFrames.data] using a20
        · simpa [copySlots,CopyFrames.data] using a21
        · simpa [copySlots,CopyFrames.data] using a2d)
  refine ⟨_,_,(d1.seq d2).seq d3,?_,?_,?_⟩
  · have h := install_slot copySlots copy_injective A2
      (CopyFrames.data (natWord n++frame t++CopyFrames.frames bs++tail) (S++CopyFrames.frames bs) n) 0
    simpa [copySlots,CopyFrames.data,src,hsrc,List.append_assoc] using h
  · have h := install_slot copySlots copy_injective A2
      (CopyFrames.data (natWord n++frame t++CopyFrames.frames bs++tail) (S++CopyFrames.frames bs) n) 1
    simpa [copySlots,CopyFrames.data,bs,frames_bottoms] using h
  · have h := dockH_slot copySlots copy_injective H2
      (CopyFrames.heads ((natWord n++frame t).length+(CopyFrames.frames bs).length) (S++CopyFrames.frames bs)) 1
    simpa [copySlots,CopyFrames.heads,bs,frames_bottoms] using h

end
end NearCubicWires.SourceStart.Circuit
