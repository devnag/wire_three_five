import W3.Recovery3.Case2Inst
import Proof.CaseAnalysis.CaseTwoNativeSourceDock
import Proof.CaseAnalysis.CaseTwoSourceCacheLayout

/-!
# The Case-2 chain, part 5: the v3 source block `blockV`

The near-cubic-wires paper ("In Case 2, apply the deterministic honest-assignment algorithm in Fact C.2 to H_{B*}"); D7
(`requestAt = requestOf`, the request on `H_B` itself once `q ≥` Fact C.2's minimum arity). The relabelled Case-2 front
`M2` (`front2_ready`: `frame (descriptor H_B)`, `1^{|H_B|}`, `1^q`, its three words kept on tapes `0, 1, 2`) docks into
proof 1's `CloseoutCaseTwo.NativeSourceDock` (as JF's `docksD`); `dockKeep` is `NativeSourceDock.source_run` with the
untouched front tapes recorded. `blockV h a` is the resulting `SBlock a`, generic over every word `oc`, every native
`B_pf` and every arity `q ≥ minArity`; `inst_req_eq` is D7's `requestOf` at the kit's instance.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicGates.Close
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

open Front

/-! ## `dockKeep` -/

/-- `NativeSourceDock.source_run` with the untouched producer tapes recorded. -/
theorem dockKeep (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (field size arity : Fin t) (hfs : field≠size) (hfa : field≠arity) (hsa : size≠arity)
    (request : PCPPRequest a.minimumArity) (fuel : ℕ) (native out : Fin t→List Bool)
    (hp : ClockJoin.ReadyRun p fuel native out)
    (hf : out field=RepairOrdinary.frame (PCPPNative.descriptor request.circuit))
    (hs : out size=List.replicate request.circuit.size true) (ha : out arity=List.replicate request.arity true) :
    ∃ r,run (NativeSourceDock.machine a p field size arity) (fuel+1+RequestSource.budget a request)
        (NativeSourceDock.input a native)=some r ∧
      r.steps≤fuel+1+RequestSource.budget a request ∧
      (∀ j,r.final.tapes (NativeSourceDock.slots a field size arity
          (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j,r.final.heads (NativeSourceDock.slots a field size arity
          (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (NativeSourceDock.slots a field size arity
          (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=RepairOrdinary.frame (pcppInput request) ∧
      r.final.heads (NativeSourceDock.slots a field size arity
          (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=0 ∧
      (∀ i : Fin t,i≠field → i≠size → i≠arity →
        r.final.tapes (NativeSourceDock.oldSlots a i)=out i ∧ r.final.heads (NativeSourceDock.oldSlots a i)=0) := by
  have prep:=hp.focus (NativeSourceDock.oldSlots a) (NativeSourceDock.old_injective a t)
    (NativeSourceDock.input a native) (by
    intro i
    simp only [NativeSourceDock.input,NativeSourceDock.oldSlots,Fin.addCases_left])
  obtain ⟨firstReceipt,hfirst,ft,fh,fs⟩:=prep
  obtain ⟨base,hb,bs,bt,bh,keep,keeph⟩:=RequestSource.source_run a request
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,lo⟩:=RecoveryFocus.dock (NativeSourceDock.slots a field size arity)
    (NativeSourceDock.slots_injective a field size arity hfs hfa hsa) (RequestSource.machine a) _
    firstReceipt.final.heads firstReceipt.final.tapes
    (initialConfiguration (RequestSource.machine a)
      (RequestSource.input a (PCPPNative.descriptor request.circuit) request.circuit.size request.arity))
    (by intro j;exact fh _)
    (by intro j;rw [ft];exact NativeSourceDock.field_input a field size arity native out _ _ _ hf hs ha j) base hb
  have he : (⟨(RequestSource.machine a).start,firstReceipt.final.heads,firstReceipt.final.tapes⟩ :
      Configuration (NativeSourceDock.tapes a t) _)=
      Composition.restart firstReceipt.final (NativeSourceDock.last a field size arity).start:=rfl
  simp only [initialConfiguration] at hl
  rw [he] at hl
  have whole:=Composition.run_join (NativeSourceDock.first a p) (NativeSourceDock.last a field size arity)
    _ _ _ firstReceipt lastReceipt hfirst hl
  refine ⟨Composition.joinedReceipt firstReceipt lastReceipt,whole,?_,?_,?_,?_,?_,?_⟩
  · change firstReceipt.steps+1+lastReceipt.steps≤_
    rw [ls]
    omega
  · intro j
    change lastReceipt.final.tapes (NativeSourceDock.slots a field size arity
      (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=_
    exact (lt _).trans (bt j)
  · intro j
    change lastReceipt.final.heads (NativeSourceDock.slots a field size arity
      (RequestSource.cacheSlots a (SourceCache.cacheSlots a j)))=_
    exact (lh _).trans (bh j)
  · change lastReceipt.final.tapes (NativeSourceDock.slots a field size arity
      (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=_
    exact (lt _).trans keep
  · change lastReceipt.final.heads (NativeSourceDock.slots a field size arity
      (RequestSource.cacheSlots a (SourceCache.requestSlot a)))=_
    exact (lh _).trans keeph
  · intro i hif his hia
    have away : ∀ j,NativeSourceDock.slots a field size arity j≠NativeSourceDock.oldSlots a i := by
      intro j hj
      have hv:=congrArg Fin.val hj
      unfold NativeSourceDock.slots at hv
      split_ifs at hv with h0 h21 h19
      · simp only [NativeSourceDock.oldSlots,Fin.val_castAdd] at hv; exact hif (Fin.ext hv.symm)
      · simp only [NativeSourceDock.oldSlots,Fin.val_castAdd] at hv; exact his (Fin.ext hv.symm)
      · simp only [NativeSourceDock.oldSlots,Fin.val_castAdd] at hv; exact hia (Fin.ext hv.symm)
      · simp only [NativeSourceDock.oldSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
        have := i.isLt
        omega
    obtain ⟨hh,htt⟩:=lo _ away
    refine ⟨?_,?_⟩
    · change lastReceipt.final.tapes (NativeSourceDock.oldSlots a i)=_
      rw [htt,ft]
      exact install_slot _ (NativeSourceDock.old_injective a t) _ _ i
    · change lastReceipt.final.heads (NativeSourceDock.oldSlots a i)=_
      rw [hh]
      exact fh _


/-! ## The instances and the block -/

/-- One instance of the v3 source block: the word of `C^O`, the native `B_pf`, its arity `q ≥ minArity`. -/
structure Inst (a : PointwisePCPPAlgorithm) where
  oc : NearCubicWires.Bindings.MW20.OracleOutput
  q : ℕ
  B : BooleanCircuit q
  hq : a.minimumArity ≤ q

/-- The request on `H_B = (C^{B_pf})` padded to its arity (D7's `requestOf` shape). -/
noncomputable def Inst.req {a : PointwisePCPPAlgorithm} (i : Inst a) : PCPPRequest a.minimumArity where
  arity := i.q
  circuit := (Outer.substCircuit i.oc.circuit i.B).padToArity
  large := i.hq
  sizeLarge := BooleanCircuit.arity_le_padToArity_size _

/-- The front's three output tapes (relabelled): `frame (descriptor H_B)`, `1^{|H_B|}`, `1^q`. -/
noncomputable def fld (h : H2D) := p2 h (tOUT UF.t h.t)
noncomputable def szs (h : H2D) := p2 h (tSZ UF.t h.t)
noncomputable def ars (h : H2D) := p2 h (tAR UF.t h.t)

theorem fld_val (h : H2D) : (fld h).val = 6 := by
  unfold fld; rw [p2_val]; rfl
theorem szs_val (h : H2D) : (szs h).val = 7 := by
  unfold szs; rw [p2_val]; rfl
theorem ars_val (h : H2D) : (ars h).val = 8 := by
  unfold ars; rw [p2_val]; rfl

theorem fld_szs (h : H2D) : fld h ≠ szs h := fun e => by have := congrArg Fin.val e; rw [fld_val, szs_val] at this; omega
theorem fld_ars (h : H2D) : fld h ≠ ars h := fun e => by have := congrArg Fin.val e; rw [fld_val, ars_val] at this; omega
theorem szs_ars (h : H2D) : szs h ≠ ars h := fun e => by have := congrArg Fin.val e; rw [szs_val, ars_val] at this; omega

theorem slots_low (a : PointwisePCPPAlgorithm) (h : H2D) (x : Fin (RequestSource.tapes a)) :
    3 ≤ (NativeSourceDock.slots a (fld h) (szs h) (ars h) x).val := by
  unfold NativeSourceDock.slots
  have hT := T2_ge h
  split_ifs
  · simp only [NativeSourceDock.oldSlots, Fin.val_castAdd, fld_val]; omega
  · simp only [NativeSourceDock.oldSlots, Fin.val_castAdd, szs_val]; omega
  · simp only [NativeSourceDock.oldSlots, Fin.val_castAdd, ars_val]; omega
  · simp only [Fin.val_natAdd]; omega

theorem common_injective (a : PointwisePCPPAlgorithm) (h : H2D) :
    Function.Injective (fun j => NativeSourceDock.slots a (fld h) (szs h) (ars h) (RequestSource.cacheSlots a j)) :=
  (NativeSourceDock.slots_injective a (fld h) (szs h) (ars h) (fld_szs h) (fld_ars h) (szs_ars h)).comp
    (RequestSource.cache_injective a)

/-- **The v3 source block** (H2′ front + proof 1's native source dock), generic in the instance. -/
noncomputable def blockV (h : H2D) (a : PointwisePCPPAlgorithm) : SBlock a where
  ι := Inst a
  req := Inst.req
  w0 i := i.oc.word
  d i := PCPPNative.descriptor i.B
  budget i := (2 * cost2 h i.oc.word.length (PCPPNative.descriptor i.B).length
      (PCPPNative.descriptor i.req.circuit).length i.q i.req.circuit.size + 2) + 1 + RequestSource.budget a i.req
  t := NativeSourceDock.tapes a (T2 h)
  st := _
  M := NativeSourceDock.machine a (M2 h) (fld h) (szs h) (ars h)
  three := by unfold NativeSourceDock.tapes; have := T2_ge h; omega
  cacheSlots j := NativeSourceDock.slots a (fld h) (szs h) (ars h) (RequestSource.cacheSlots a (SourceCache.cacheSlots a j))
  requestSlot := NativeSourceDock.slots a (fld h) (szs h) (ars h) (RequestSource.cacheSlots a (SourceCache.requestSlot a))
  cache_injective := by
    intro i j he
    have hc := common_injective a h he
    have hb := SourceCache.cold_injective a hc
    have hi := PCPPQueryCold.bank_injective (SourceCache.degree a) hb
    exact Fin.ext (congrArg (fun x : Fin 21 => x.val) hi)
  cache_request := fun j he => SourceCache.cold_away a _ (common_injective a h he)
  cache_low := fun j => slots_low a h _
  request_low := slots_low a h _
  run := by
    intro i address
    obtain ⟨out, hrun, hO, hS, hA, hk⟩ := front2_ready h i.oc i.B address
    obtain ⟨r, hr, hsteps, hc, hch, hq, hqh, hold⟩ := dockKeep a (M2 h) (fld h) (szs h) (ars h)
      (fld_szs h) (fld_ars h) (szs_ars h) i.req _ _ out hrun hO hS hA
    have hin : XorFamily.wordInput (t := NativeSourceDock.tapes a (T2 h))
        ![i.oc.word, RepairOrdinary.frame (PCPPNative.descriptor i.B), RepairOrdinary.frame address] =
        NativeSourceDock.input a (XorFamily.wordInput (t := T2 h)
          ![i.oc.word, RepairOrdinary.frame (PCPPNative.descriptor i.B), RepairOrdinary.frame address]) :=
      (XorFamily.extend_words (by have := T2_ge h; omega) _).symm
    have low (k : Fin 3) : (⟨k.val, by have := k.isLt; have := T2_ge h; omega⟩ : Fin (T2 h)) ≠ fld h ∧
        (⟨k.val, by have := k.isLt; have := T2_ge h; omega⟩ : Fin (T2 h)) ≠ szs h ∧
        (⟨k.val, by have := k.isLt; have := T2_ge h; omega⟩ : Fin (T2 h)) ≠ ars h := by
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> have hv := congrArg Fin.val e <;>
        simp only [fld_val, szs_val, ars_val] at hv <;> have := k.isLt <;> omega
    refine ⟨r, ?_, hsteps, hc, hch, hq, hqh, ?_, ?_⟩
    · rw [hin]; exact hr
    · intro k
      have e : (⟨k.val, by have := k.isLt; have := T2_ge h; unfold NativeSourceDock.tapes; omega⟩ :
          Fin (NativeSourceDock.tapes a (T2 h))) =
          NativeSourceDock.oldSlots a ⟨k.val, by have := k.isLt; have := T2_ge h; omega⟩ := Fin.ext rfl
      rw [e]
      exact ((hold _ (low k).1 (low k).2.1 (low k).2.2).1).trans (hk k)
    · intro k
      have e : (⟨k.val, by have := k.isLt; have := T2_ge h; unfold NativeSourceDock.tapes; omega⟩ :
          Fin (NativeSourceDock.tapes a (T2 h))) =
          NativeSourceDock.oldSlots a ⟨k.val, by have := k.isLt; have := T2_ge h; omega⟩ := Fin.ext rfl
      rw [e]
      exact (hold _ (low k).1 (low k).2.1 (low k).2.2).2

end W3.NearCubicWires.RepairSource.Outer3.Case2
