import Proof.CaseAnalysis.RowsCircuitMode

/-! Complete cold circuit framing, fixed canonical family tag and actual
bottom-list count. The original ordered gate stream and top code are retained
for the full circuit worker; no circuit is reencoded for this decision. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPrefix
open LocalBitMultitape RecoveryRootRound RadixSemantics PCPPNativeCanonicalTree
open CanonicalBinary CloseoutRowsCircuitHeader
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 268) : Fin 639:=i.castAdd 371
def countSlots (i : Fin 368) : Fin 639:=
  if i.val=0 then 118 else if i.val=174 then 78 else
    ⟨if i.val<174 then 267+i.val else 266+i.val,by split_ifs <;> omega⟩
def modeSlots (i : Fin 5) : Fin 639:=if i.val=0 then 38 else ⟨633+i.val,by omega⟩
def flagSlots : Fin 4→Fin 639:=![267,633,635,638]
def input (bits : List Bool) : Fin 639→List Bool:=
  Fin.addCases (m:=268) (n:=371) (motive:=fun _=>List Bool)
    (CloseoutRowsCircuitTagged.input bits) (fun _=>[])
noncomputable def header:=RecoveryFocus.machine old CloseoutRowsCircuitTagged.machine
noncomputable def counter:=RecoveryFocus.machine countSlots CloseoutRowsCircuitCount.machine
noncomputable def mode (threshold : Bool):=RecoveryFocus.machine modeSlots (CloseoutRowsCircuitMode.machine threshold)
noncomputable def finish:=RecoveryFocus.machine flagSlots CloseoutRowsCircuitCount.fold
noncomputable def phase1:=Composition.machine header counter
noncomputable def phase2 (threshold : Bool):=Composition.machine phase1 (mode threshold)
noncomputable def machine (threshold : Bool):=Composition.machine (phase2 threshold) finish
def budget (bits : List Bool):=CloseoutRowsCircuitTagged.budget bits+
  CloseoutRowsCircuitCount.budget (codeWord bits 2) (codeWord bits 1)+
  CloseoutRowsCircuitMode.budget (codeWord bits 0)+4
def valid (threshold : Bool) (bits : List Bool) : Prop:=
  structural bits ∧ decodeNat (value (codeWord bits 0))=some threshold.toNat ∧
    ∃ values,decodeBalancedList (value (codeWord bits 2))=some values ∧
      decodeNat (value (codeWord bits 1))=some values.length

theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 639=>k.val) h)
theorem count_val (i : Fin 368) : (countSlots i).val=
    if i.val=0 then 118 else if i.val=174 then 78 else
      if i.val<174 then 267+i.val else 266+i.val:=by
  unfold countSlots;split_ifs <;> rfl
theorem count_injective : Function.Injective countSlots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 639=>k.val) h
  rw [count_val,count_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem mode_injective : Function.Injective modeSlots:=by decide
theorem count_outside (i : Fin 639) (hi:i.val<268) (h78:i≠78) (h118:i≠118) :
    ∀ j,countSlots j≠i:=by
  intro j he;have hv:=congrArg (fun k : Fin 639=>k.val) he
  simp only [countSlots] at hv
  split_ifs at hv with h0 h174 hlt
  · exact h118 (Fin.ext hv.symm)
  · exact h78 (Fin.ext hv.symm)
  · change 267+j.val=i.val at hv;omega
  · change 266+j.val=i.val at hv;omega
theorem count_after (i : Fin 639) (hi:634 ≤ i.val) : ∀ j,countSlots j≠i:=by
  intro j he;have hv:=congrArg (fun k : Fin 639=>k.val) he
  simp only [countSlots] at hv
  split_ifs at hv <;> simp_all <;> omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitPrefix
