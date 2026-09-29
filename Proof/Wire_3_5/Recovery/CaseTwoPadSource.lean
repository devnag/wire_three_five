import Proof.Wire_3_5.Recovery.CaseTwoPad

/-! # The padded request's descriptor and PCPP source (P3:3761-3763; D1.6, Case 2 of the hybrid)

Realizes "each honest proof bit is computed by the deterministic PCPP algorithm" (P3:3762-3763) on `S₂`'s padded
request, one level up from `Proof.Wire_3_5.Recovery.CaseTwoPad`: base's descriptor consumer (`PCPPNativeClauseDescriptorConsumer`,
generic in the producer and the circuit) framed on the padded producer writes the descriptor of
`request a (castCircuit hq c)`, its arity `1^{domain a q}` and size; base's `NativeSourceDock` (generic in the
descriptor machine and the request) then runs base's `RequestSource`/`SourceCache` on that request, i.e. computes the
PCPP output of the padded request.

Paper quantity: the PCPP output of the padded request; **`pmachine`** / **`pdescriptor_run`** (the padded descriptor)
and **`omachine`** / **`osource_run`** (the padded source: the clause data of `a.output request` and `frame (pcppInput
request)` for `request = PCPPRequestBoundary.request a (castCircuit hq c)`), with the input `oinput` by values
(`oinput_val`: the framed hierarchy/oracle word on tape 0 and `1^q` on the producer's extra tape). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-! ## The padded descriptor -/

def pwidth (k : ℕ) : Fin (PCPPNativeHierarchyNodes.tapes source k + 5) :=
  (PCPPNativeHierarchyNodes.slots source k 72).castAdd 5
def psize (k : ℕ) : Fin (PCPPNativeHierarchyNodes.tapes source k + 5) :=
  (PCPPNativeHierarchyNodes.slots source k 91).castAdd 5
def pindex (k : ℕ) : Fin (PCPPNativeHierarchyNodes.tapes source k + 5) :=
  (PCPPNativeHierarchyNodes.slots source k 89).castAdd 5
def ptarget (k : ℕ) := PCPPNativeClauseDescriptorConsumer.slots (pwidth source k) (psize source k) (pindex source k) 26
def pnative (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  PCPPNativeClauseDescriptorConsumer.machine a (padProducer source k CH Cpad code) (padTarget source k)
    (pwidth source k) (psize source k) (pindex source k)
def pbase (k : ℕ) := PCPPNativeClauseDescriptorConsumer.tapes (PCPPNativeHierarchyNodes.tapes source k + 5)
def ptapes (k : ℕ) := (pbase source k + 2) + 2
def pframeSlot (k : ℕ) : Fin (ptapes source k) := (0 : Fin 2).natAdd (pbase source k + 2)
def parity (k : ℕ) := PCPPNativeFrame.old
  (PCPPNativeClauseDescriptorConsumer.slots (pwidth source k) (psize source k) (pindex source k) 10)
def psizeSlot (k : ℕ) := PCPPNativeFrame.old
  (PCPPNativeClauseDescriptorConsumer.slots (pwidth source k) (psize source k) (pindex source k) 27)
/-- **The padded descriptor machine.** -/
def pmachine (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  AppendOutputFrame.machine (pnative source a k CH Cpad code) (ptarget source k)
def pinput (k : ℕ) (hierarchy oracle : List Bool) (q : ℕ) :=
  AppendOutputFrame.input (PCPPNativeClauseDescriptorConsumer.input
    (padInput source k (SourceHandoff.sourceTapes (PCPPNativeInputFields.word hierarchy oracle)) q))
def pbudget (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :=
  2 * PCPPNativeClauseDescriptorConsumer.budget a (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k
      H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))
      (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle + 1 + widthFixCost q) +
    4 * (PCPPNative.descriptor (PCPPRequestBoundary.request a (castCircuit hq (PCPPNativeHierarchyNodes.circuit source
      k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))).circuit).length + 7

theorem scalars_distinct (k : ℕ) : pwidth source k ≠ psize source k ∧ pwidth source k ≠ pindex source k ∧
    psize source k ≠ pindex source k := by
  obtain ⟨h1, h2, h3⟩ := PCPPNativeHierarchyNodes.scalar_distinct source k
  exact ⟨fun h => h1 (Fin.castAdd_injective _ _ h), fun h => h2 (Fin.castAdd_injective _ _ h),
    fun h => h3 (Fin.castAdd_injective _ _ h)⟩

/-- **The padded descriptor is ready**: the frame of the padded request's descriptor, its arity and its size. -/
theorem pdescriptor_run (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :
    ∃ out, ClockJoin.ReadyRun (pmachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (pbudget source a H Cpad hpad r oracle q hq)
      (pinput source k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) q) out ∧
      out (pframeSlot source k) = RepairOrdinary.frame (PCPPNative.descriptor (PCPPRequestBoundary.request a (castCircuit hq
        (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
          oracle))).circuit) ∧
      out (parity source k) = List.replicate (PCPPRequestBoundary.request a (castCircuit hq
        (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
          oracle))).arity true ∧
      out (psizeSlot source k) = List.replicate (PCPPRequestBoundary.request a (castCircuit hq
        (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
          oracle))).circuit.size true := by
  obtain ⟨nodes, hn, nt, nh, ni, ns, nw⟩ := padProducer_run source H Cpad hcoeff hpad r oracle q hq
  have hd := scalars_distinct source k
  obtain ⟨nativeResult, hr, hs, ht, hh, _, ha, _, hz⟩ := PCPPNativeClauseDescriptorConsumer.descriptor_run a
    (padProducer source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (padTarget source k) (pwidth source k) (psize source k) (pindex source k) hd.1 hd.2.1 hd.2.2
    (padProducer_forward source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    _ _ _ nodes hn nt nh nw ns ni
  have forward := PCPPNativeClauseDescriptorConsumer.forward a
    (padProducer source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (padTarget source k) (pwidth source k) (psize source k) (pindex source k) hd.1 hd.2.1 hd.2.2
  obtain ⟨result, rr, rt, rh, keep, rs⟩ := PCPPNativeFrame.frame_run
    (pnative source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (ptarget source k) forward _ _ nativeResult hr _ ht hh
  refine ⟨result.final.tapes, ClockJoin.enlarge _ _ _ _ _ ⟨result, rr, rfl, rh, rs⟩
    (by dsimp only [pbudget]; omega), rt, ?_, ?_⟩
  · exact (keep _).trans ha
  · exact (keep _).trans hz

/-! ## The padded source -/

theorem slots_distinct (k : ℕ) : pframeSlot source k ≠ psizeSlot source k ∧ pframeSlot source k ≠ parity source k ∧
    psizeSlot source k ≠ parity source k := by
  have vals : (pframeSlot source k).val = PCPPNativeHierarchyNodes.tapes source k + 5 + 71 ∧
      (psizeSlot source k).val = PCPPNativeHierarchyNodes.tapes source k + 5 + 31 ∧
      (parity source k).val = PCPPNativeHierarchyNodes.tapes source k + 5 + 14 := by
    simp [pframeSlot, psizeSlot, parity, pbase, PCPPNativeClauseDescriptorConsumer.tapes,
      PCPPNativeClauseDescriptorConsumer.slots, PCPPNativeFrame.old, Nat.add_assoc]
  refine ⟨?_, ?_, ?_⟩
  all_goals intro he; have hv := congrArg Fin.val he; omega

def otapes (a : PointwisePCPPAlgorithm) (k : ℕ) := NativeSourceDock.tapes a (ptapes source k)
/-- **The padded source**: the padded descriptor, then base's request source on it. -/
def omachine (a : PointwisePCPPAlgorithm) (k CH Cpad : ℕ) (code : List Bool) :=
  NativeSourceDock.machine a (pmachine source a k CH Cpad code) (pframeSlot source k) (psizeSlot source k)
    (parity source k)
def oinput (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy oracle : List Bool) (q : ℕ) :=
  NativeSourceDock.input a (pinput source k hierarchy oracle q)
def oslots (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (RequestSource.tapes a)) :=
  NativeSourceDock.slots a (pframeSlot source k) (psizeSlot source k) (parity source k) j
def obudget (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :=
  pbudget source a H Cpad hpad r oracle q hq + 1 + RequestSource.budget a (PCPPRequestBoundary.request a
    (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
      r.2 hpad oracle)))

/-- **The padded source is ready**: the clause data of the PCPP output of the padded request and its framed input. -/
theorem osource_run (a : PointwisePCPPAlgorithm) {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :
    let request := PCPPRequestBoundary.request a (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k
      H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))
    ∃ result, run (omachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (obudget source a H Cpad hpad r oracle q hq)
      (oinput source a k (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) q) = some result ∧
      result.steps ≤ obudget source a H Cpad hpad r oracle q hq ∧
      (∀ j, result.final.tapes (oslots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))) =
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size + request.arity)) [] j) ∧
      (∀ j, result.final.heads (oslots source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))) =
        PCPPQueryClauseReuse.heads j) ∧
      result.final.tapes (oslots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a))) =
        RepairOrdinary.frame (pcppInput request) ∧
      result.final.heads (oslots source a k (RequestSource.cacheSlots a (SourceCache.requestSlot a))) = 0 := by
  obtain ⟨out, hr, hf, ha, hs⟩ := pdescriptor_run source a H Cpad hcoeff hpad r oracle q hq
  exact NativeSourceDock.source_run a (pmachine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (pframeSlot source k) (psizeSlot source k) (parity source k)
    (slots_distinct source k).1 (slots_distinct source k).2.1 (slots_distinct source k).2.2 _ _ _ out hr hf hs ha

/-! ## The padded source's input by values -/

theorem addCases_val {m n : ℕ} (f : Fin m → List Bool) (g : Fin n → List Bool) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => List Bool) f g i =
      if h : i.val < m then f ⟨i.val, h⟩ else g ⟨i.val - m, by have := i.isLt; omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
  · simp

theorem padInput_val (k : ℕ) (word : List Bool) (q : ℕ) (j : Fin (PCPPNativeHierarchyNodes.tapes source k + 5)) :
    padInput source k (SourceHandoff.sourceTapes word) q j =
      if j.val = 0 then word else if j.val = PCPPNativeHierarchyNodes.tapes source k then List.replicate q true
      else [] := by
  have ht : 438 ≤ PCPPNativeHierarchyNodes.tapes source k := by unfold PCPPNativeHierarchyNodes.tapes; omega
  unfold padInput
  refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
  · have := j'.isLt
    simp only [Fin.addCases_left, SourceHandoff.sourceTapes, Fin.val_castAdd]
    split_ifs <;> first | rfl | omega
  · fin_cases l <;> (simp; try omega)

/-- **The padded source's input**: the framed hierarchy/oracle word on tape 0 and `1^q` on the producer's extra
tape (index `PCPPNativeHierarchyNodes.tapes source k`); every other tape is empty. -/
theorem oinput_val (a : PointwisePCPPAlgorithm) (k : ℕ) (hierarchy oracle : List Bool) (q : ℕ)
    (i : Fin (otapes source a k)) :
    oinput source a k hierarchy oracle q i =
      if i.val = 0 then PCPPNativeInputFields.word hierarchy oracle
      else if i.val = PCPPNativeHierarchyNodes.tapes source k then List.replicate q true else [] := by
  have hi := i.isLt
  simp only [otapes, NativeSourceDock.tapes, ptapes, pbase, PCPPNativeClauseDescriptorConsumer.tapes] at hi
  have ht : 438 ≤ PCPPNativeHierarchyNodes.tapes source k := by unfold PCPPNativeHierarchyNodes.tapes; omega
  simp only [oinput, NativeSourceDock.input, pinput, AppendOutputFrame.input, AppendOutputLength.input,
    PCPPNativeClauseDescriptorConsumer.input, addCases_val, padInput_val, PCPPNativeClauseDescriptorConsumer.tapes]
  split_ifs <;> first | rfl | omega

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
