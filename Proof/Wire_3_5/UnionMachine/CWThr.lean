import Proof.Wire_3_5.UnionMachine.CWBoundsT
import Proof.Wire_3_5.UnionMachine.CWPack

/-! # C6 front, U5, the code writers: the carrier writer of the `THR∘THR` mode

"It then selects the common star translation, constructs the shared coordinate filters" (P3:3673-3674): the union
front writes each call's named carrier `Stars.Carrier.code (carrierOf .thr cs)`. The charged gates of a `THR∘THR`
circuit are its bottoms at the top's support (`Stars.thrGates`), so the `THR∘THR` core keeps exactly those:
* a circuit's field 3 is its top's code, whose field 2 is the support bitmap (`top_thr`, `supw_thr`, base's gate
  fields); the selectors are the bitmap's bits (`sels_thr`), one per bottom (`sels_len`);
* the retained bottom words are the bottoms at the support (`bwT_thr`), whose atom codes are the gate codes of
  `thrGates` (`bwT_gc_thr`);
* **`code_thr`**: the serializer's code of the retained atom codes is `Carrier.code (carrierOf .thr cs)`;
* **`thr_ready`**, **`thrCarrierWriter : CarrierWriterJ .thr`**, within `(Kc + 3)·(|u| + q + 1)^26`;
* **`carrierWriters : ∀ m, CarrierWriterJ m`** (with FP's `SYM∘THR` writer, `CWPack.symCarrierWriter`).

Paper quantity of the main type: the code of the named carrier of a list of `THR∘THR` circuits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWThr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.CanonicalBinary
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires.WireExponent3_5.UnionMachine.CWSel (selOf selOf_cons selBit)
open NearCubicWires.WireExponent3_5.UnionMachine.CWRoundT (top supw sels pairs bwT)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMainT
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters NearCubicWires.WireExponent3_5.UnionMachine.CWIface
open NearCubicWires.WireExponent3_5.PrimT.CarrierFormat (gateCode)

/-! ## The fields of a `THR∘THR` circuit code -/

theorem fld_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    value (CWRoundA.fld (encodeNormalizedThresholdThresholdCircuit C)) =
      encodeBalancedList (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)) :=
  CWSym.fld_value _ (encodeNat thresholdCircuitFamilyTag) (encodeNat C.bottomCount) _
    (encodeSupportedNormalizedGate C.top) rfl

/-- The top's field is the top's code. -/
theorem top_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    value (top (encodeNormalizedThresholdThresholdCircuit C)) = encodeSupportedNormalizedGate C.top := by
  have := CloseoutRowsCircuitHeader.code_values (encodeNat thresholdCircuitFamilyTag) (encodeNat C.bottomCount)
    (encodeBalancedList (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)))
    (encodeSupportedNormalizedGate C.top) (pay (encodeNormalizedThresholdThresholdCircuit C)) (by rw [value_pay]; rfl) 3
  show value (CloseoutRowsCircuitHeader.codeWord (pay _) 3) = _
  simpa using this

/-- The top's support field is the support bitmap. -/
theorem supw_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    value (supw (encodeNormalizedThresholdThresholdCircuit C)) =
      encodeBoolList (CloseoutRowsGateSupport.gateMembers C.top.support) := by
  obtain ⟨-, hc⟩ := CloseoutRowsGateFieldsMeaning.field_codes C.top _ (top_thr C)
  have := hc 2
  show value (CloseoutRowsGateHeader.codeWord (top _) 2) = _
  simpa [CloseoutRowsGateFieldsMeaning.codes] using this

/-- **The selectors are the support's bits**, at the support field's width. -/
theorem sels_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    sels (encodeNormalizedThresholdThresholdCircuit C) =
      ((CloseoutRowsGateSupport.gateMembers C.top.support).map boolCode).map
        (binary (supw (encodeNormalizedThresholdThresholdCircuit C)).length) := by
  unfold sels
  rw [supw_thr]
  unfold encodeBoolList
  rw [PCPPNativeCanonicalTree.tree_atoms]

/-- **The bottoms' words**, at the bottoms field's width. -/
theorem bw_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    CWRoundA.bw (encodeNormalizedThresholdThresholdCircuit C) =
      (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)).map
        (binary (CWRoundA.fld (encodeNormalizedThresholdThresholdCircuit C)).length) :=
  CWSym.bw_of _ _ (fld_thr C)

/-! ## The selection, over abstract codes -/

theorem zip_maps {α β γ : Type} (f : α → β) (g : α → γ) : ∀ l : List α,
    (l.map f).zip (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp [zip_maps f g l]

theorem selOf_map {α : Type} (f g : α → List Bool) : ∀ l : List α,
    selOf (l.map fun a => (f a, g a)) = (l.filter fun a => selBit (g a)).map f
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, selOf_cons, selOf_map f g l]
    by_cases h : selBit (g a) = true
    · simp [List.filter_cons, h]
    · simp [List.filter_cons, h]

theorem selBit_binary (W : ℕ) (hW : 1 ≤ W) (b : Bool) : selBit (binary W (boolCode b)) = b := by
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  cases b <;> rfl

/-- **The selection keeps the codes at the support**, for any codes `f` and widths `W`, `V ≥ 1`. -/
theorem sel_support {k : ℕ} (f : Fin k → ℕ) (S : Finset (Fin k)) (W V : ℕ) (hV : 1 ≤ V) :
    selOf (((List.ofFn f).map (binary W)).zip
      (((CloseoutRowsGateSupport.gateMembers S).map boolCode).map (binary V))) =
      ((List.finRange k).filter fun i => decide (i ∈ S)).map fun i => binary W (f i) := by
  unfold CloseoutRowsGateSupport.gateMembers
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.map_map, List.map_map, List.map_map, zip_maps, selOf_map]
  congr 1
  apply List.filter_congr
  intro i _
  exact selBit_binary V hV _

theorem sels_len {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    (sels (encodeNormalizedThresholdThresholdCircuit C)).length =
      (CWRoundA.bw (encodeNormalizedThresholdThresholdCircuit C)).length := by
  rw [sels_thr, bw_thr]
  unfold CloseoutRowsGateSupport.gateMembers
  simp only [List.length_map, List.length_ofFn]

/-! ## The retained bottoms -/

/-- **The retained bottom words are the bottoms at the top's support.** -/
theorem bwT_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    bwT (encodeNormalizedThresholdThresholdCircuit C) =
      ((List.finRange C.bottomCount).filter fun i => decide (i ∈ C.top.support)).map fun i =>
        binary (CWRoundA.fld (encodeNormalizedThresholdThresholdCircuit C)).length
          (encodeSupportedNormalizedGate (C.bottom i)) := by
  unfold bwT pairs
  rw [bw_thr, sels_thr]
  exact sel_support (fun i => encodeSupportedNormalizedGate (C.bottom i)) C.top.support _ _
    (by rw [CWRoundT.supw_length]; exact natBitLength_pos _)

/-- A list of indexed words, each an atom code's word: their atom codes. -/
theorem map_gc_idx {k : ℕ} (w : Fin k → List Bool) (g : Fin k → ℕ) (h : ∀ i, CWRoundB.gc (w i) = g i) :
    ∀ l : List (Fin k), (l.map w).map CWRoundB.gc = l.map g
  | [] => rfl
  | i :: l => by rw [List.map_cons, List.map_cons, List.map_cons, h i, map_gc_idx w g h l]

/-- **The retained bottoms' atom codes are the codes of the charged gates.** -/
theorem bwT_gc_thr {q : ℕ} (C : NormalizedThresholdThresholdCircuit q) :
    (bwT (encodeNormalizedThresholdThresholdCircuit C)).map CWRoundB.gc = (Stars.thrGates C).map gateCode := by
  rw [bwT_thr, PrimT.CarrierFormat.thrGates_codes]
  refine map_gc_idx _ (fun i => gateCode (C.bottom i).gate) (fun i => ?_) _
  have hlt := CWSym.atom_lt _ _ (fld_thr C) (encodeSupportedNormalizedGate (C.bottom i)) (by
    rw [List.mem_ofFn]; exact ⟨i, rfl⟩)
  exact CWSym.gc_bottom _ (C.bottom i) hlt

theorem botsT_eq (xs : List ℕ) : botsT xs = (xs.map bwT).flatten := by
  simp [botsT, CWRoundT.bacT]

theorem botsT_gc_thr {q : ℕ} (cs : List (NormalizedThresholdThresholdCircuit q)) :
    (botsT (cs.map (Mode.code .thr))).map CWRoundB.gc = (carrierOf .thr cs).map gateCode := by
  rw [botsT_eq, List.map_flatten, List.map_map, List.map_map]
  unfold carrierOf
  rw [List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro C _
  exact bwT_gc_thr C

/-- **The serializer's code is the carrier code.** -/
theorem code_thr {q : ℕ} (cs : List (NormalizedThresholdThresholdCircuit q)) :
    PCPTraversal.code (codesT (cs.map (Mode.code .thr))) = Stars.Carrier.code (carrierOf .thr cs) := by
  have h1 : PCPTraversal.code (codesT (cs.map (Mode.code .thr))) =
      encodeBalancedList ((codesT (cs.map (Mode.code .thr))).map RadixSemantics.value) := rfl
  rw [h1, CWBoundsT.codesT_eq, CWSym.values_bits, botsT_gc_thr]
  exact (PrimT.CarrierFormat.code_eq _).symm

theorem hsel_thr {q : ℕ} (cs : List (NormalizedThresholdThresholdCircuit q)) :
    ∀ x ∈ cs.map (Mode.code .thr), (sels x).length = (CWRoundA.bw x).length := by
  intro x hx
  obtain ⟨C, -, rfl⟩ := List.mem_map.mp hx
  exact sels_len C

/-! ## The writer -/

theorem codesWord_thr {q : ℕ} (cs : List (NormalizedThresholdThresholdCircuit q)) :
    codesWord .thr cs = ((cs.map (Mode.code .thr)).map natWord).flatten := by
  unfold codesWord; rw [List.map_map]; rfl

theorem inBank_eqT (u : List Bool) : inBank (0 : Fin 1233) u = coreTIn u := by
  funext j; unfold inBank coreTIn
  by_cases h : j = 0
  · subst h; simp
  · have h' : ¬ j.val = 0 := fun e => h (Fin.ext e)
    rw [if_neg h, if_neg h']

theorem outBank_eqT (u v : List Bool) (tout : Fin 1233 → List Bool) (h0 : tout 0 = frame u) (h1 : tout 1 = frame v) :
    outBankJ 0 1 u v tout = tout := by
  funext j; unfold outBankJ
  by_cases e0 : j = 0
  · subst e0; simp [h0]
  · by_cases e1 : j = 1
    · subst e1; simp [h1]
    · simp [e0, e1]

/-- **The `THR∘THR` carrier writer's run.** -/
theorem thr_ready (q : ℕ) (cs : List (NormalizedThresholdThresholdCircuit q)) :
    ∃ J : Fin 1233 → List Bool, (∀ j, (J j).length ≤ (CWBounds.Kc + 3) * ((codesWord .thr cs).length + q + 1) ^ 26) ∧
      ClockJoin.ReadyRun coreTM ((CWBounds.Kc + 3) * ((codesWord .thr cs).length + q + 1) ^ 26)
        (inBank 0 (codesWord .thr cs))
        (outBankJ 0 1 (codesWord .thr cs) (natWord (Stars.Carrier.code (carrierOf .thr cs))) J) := by
  have hu : codesWord .thr cs = ((cs.map (Mode.code .thr)).map natWord).flatten := codesWord_thr cs
  have hs := hsel_thr cs
  obtain ⟨tout, st, h0, h1⟩ := coreT_step (cs.map (Mode.code .thr)) hs (CWBoundsT.capsT_ok _ hs)
  have hcost := CWBoundsT.coreTCost_le (cs.map (Mode.code .thr)) hs
  rw [code_thr cs] at h1
  rw [← hu] at h0 hcost st
  have hr := FrontKit.ready_of_step st
  generalize codesWord .thr cs = u at *
  have hP1 : (u.length + 1) ^ 26 ≤ (u.length + q + 1) ^ 26 := Nat.pow_le_pow_left (by omega) _
  have hP2 : u.length + 1 ≤ (u.length + q + 1) ^ 26 :=
    (Nat.le_self_pow (by norm_num) _).trans hP1
  have hlen := NearCubicWires.WireExponent3_5.Transfer.ready_lengths hr (2 * u.length + 1) (by
    intro i; unfold coreTIn; split_ifs
    · rw [frame_eq_frameP]; simp
    · simp)
  generalize (u.length + q + 1) ^ 26 = P at *
  have h1' := Nat.mul_le_mul_left CWBounds.Kc hP1
  have e : (CWBounds.Kc + 3) * P = CWBounds.Kc * P + 3 * P := by ring
  refine ⟨tout, fun j => ?_, ?_⟩
  · have := hlen j
    rw [e]; omega
  · rw [inBank_eqT, outBank_eqT _ _ tout h0 h1]
    exact ClockJoin.enlarge _ _ _ _ _ hr (by rw [e]; omega)

/-- **The `THR∘THR` carrier writer.** -/
noncomputable def thrCarrierWriter : CarrierWriterJ .thr :=
  CWPack.carrierWriterOf .thr coreTM 0 1 (by decide) (CWBounds.Kc + 3) 26 thr_ready

/-- **The carrier writers of both class modes** (the `carrier` field of `CWIface.WritersJ`). -/
noncomputable def carrierWriters : (m : Mode) → CarrierWriterJ m
  | .thr => thrCarrierWriter
  | .sym => CWPack.symCarrierWriter

end NearCubicWires.WireExponent3_5.UnionMachine.CWThr
