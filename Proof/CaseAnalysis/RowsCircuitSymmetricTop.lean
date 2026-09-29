import Proof.CaseAnalysis.RowsCircuitThresholdTop
import Proof.CaseAnalysis.RowsCircuitSymTop

/-! Total symmetric top check and publication at the frozen circuit ports.
The actual bottom count is copied once; the Boolean table is never parsed
again and the original domain template remains available for the loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 181) : Fin 1703:=
  if i.val=0 then 640 else if i.val=1 then 639 else if i.val=178 then 624 else
    if i.val=179 then 1676 else if i.val=180 then 1687 else ⟨639+i.val,by omega⟩
def publishSlots : Fin 12→Fin 1703:=![813,1691,1680,1684,622,1694,1695,1701,1692,1702,1689,1696]
def external : Fin 11→Fin 1703:=![1691,1680,1684,622,1694,1695,1701,1692,1702,1689,1696]
def externalData (cap m : ℕ) : Fin 11→List Bool:=
  ![List.replicate cap false,List.replicate cap false,List.replicate cap false,List.replicate m true,
    List.replicate cap true,List.replicate (cap+1) false,List.replicate cap false,
    List.replicate cap false,List.replicate cap false,[],List.replicate cap false]
def pads (cap : ℕ) (i : Fin 181):=if i.val=178 then 0 else cap
def padded (cap : ℕ) (A : Fin 181→List Bool) (i : Fin 181):=ZeroPadding.pad (pads cap i) (A i)
def sources (cap m : ℕ) (bits : List Bool) : Fin 3→List Bool:=
  ![ZeroPadding.pad cap (frame (BitFields.payload bits)),List.replicate cap false,List.replicate m true]
noncomputable def parser:=RecoveryFocus.machine slots CloseoutRowsCircuitSymTop.machine
noncomputable def publisher:=RecoveryFocus.machine publishSlots CloseoutRowsCircuitTopPublish.machine
noncomputable def machine:=CloseoutRowsGateColdPair.machine parser publisher (fun b=>b 1676)
def budget (cap : ℕ) (bits : List Bool):=CloseoutRowsCircuitSymTop.budget bits+8*cap+22
noncomputable def middle (cap : ℕ) (A : Fin 1703→List Bool) (bank : Fin 181→List Bool):=
  install slots A (padded cap bank)
noncomputable def output (cap m : ℕ) (bits : List Bool) (A : Fin 1703→List Bool) (bank : Fin 181→List Bool):=
  install publishSlots (middle cap A bank) (CloseoutRowsCircuitTopPublish.output cap 0 0 (sources cap m bits))

theorem slots_val (i : Fin 181) : (slots i).val=
    if i.val=0 then 640 else if i.val=1 then 639 else if i.val=178 then 624 else
      if i.val=179 then 1676 else if i.val=180 then 1687 else 639+i.val:=by
  unfold slots;split_ifs <;> rfl
theorem slots_injective : Function.Injective slots:=by
  intro i j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [slots_val,slots_val] at hv
  apply Fin.ext;split_ifs at hv <;> omega
theorem external_outside (i : Fin 11) : ∀ j,slots j≠external i:=by
  have range:(external i).val=622 ∨ 1680 ≤ (external i).val ∧ (external i).val≠1687:=by
    fin_cases i <;> decide
  intro j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [slots_val] at hv;split_ifs at hv <;> omega
theorem publish_injective : Function.Injective publishSlots:=by decide

theorem input_eq (m : ℕ) (bits : List Bool) (i : Fin 181) : CloseoutRowsCircuitSymTop.input m bits i=
    if i.val=178 then UnaryTemplate.tape m else if i.val=0 then frame bits else []:=by
  refine Fin.addCases (m:=178) (n:=3) ?_ ?_ i
  · intro j
    simp only [CloseoutRowsCircuitSymTop.input,Fin.addCases_left,Fin.val_castAdd,
      if_neg (show j.val≠178 by omega)]
    refine Fin.addCases (m:=174) (n:=4) ?_ ?_ j
    · intro k
      simp only [NatCold.input,Fin.addCases_left,Fin.val_castAdd]
      rfl
    · intro k
      simp only [NatCold.input,Fin.addCases_right,Fin.val_natAdd,
        if_neg (show 174+k.val≠0 by omega)]
  · intro j;fin_cases j <;> rfl

theorem padded_run (cap m : ℕ) (bits : List Bool) (hin : 2*bits.length+1≤cap)
    (hcap : CloseoutRowsCircuitSymTop.budget bits+1≤cap) : ∃ bank,
    ClockJoin.ReadyRun CloseoutRowsCircuitSymTop.machine (CloseoutRowsCircuitSymTop.budget bits)
      (padded cap (CloseoutRowsCircuitSymTop.input m bits)) (padded cap bank) ∧
      bank 174=frame (BitFields.payload bits) ∧ bank 178=UnaryTemplate.tape m ∧
      (readTapeBit (bank 179) 0=true ↔ CloseoutRowsCircuitSymTop.valid m bits) ∧
      ∀ i : Fin 181,i.val≠178 → (padded cap bank i).length≤cap:=by
  obtain ⟨bank,⟨base,hbase,bt,bh,bs⟩,table,count,flag⟩:=CloseoutRowsCircuitSymTop.top_run m bits
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CloseoutRowsCircuitSymTop.machine (pads cap) _ _ base hbase
  refine ⟨bank,⟨r,hr,?_,?_,rs ▸ bs⟩,table,count,flag,?_⟩
  · rw [rf];change (fun i=>ZeroPadding.pad (pads cap i) (base.final.tapes i))=_
    rw [bt];rfl
  · intro i;rw [rf];exact bh i
  · intro i hi
    have bound:=PCPSerializerReuse.tape_support CloseoutRowsCircuitSymTop.machine _ _ r hr i cap 0 (by rfl)
      (by
        change (padded cap (CloseoutRowsCircuitSymTop.input m bits) i).length ≤ max cap (0+1)
        simp only [padded,ZeroPadding.pad_length,input_eq,pads,if_neg hi]
        apply max_le
        · exact Nat.le_max_left _ _
        · split_ifs
          · exact (frame_length bits ▸ hin).trans (Nat.le_max_left _ _)
          · exact Nat.zero_le _)
    rw [rf,rs] at bound
    change (ZeroPadding.pad (pads cap i) (base.final.tapes i)).length≤_ at bound
    rw [bt] at bound
    simpa only [padded,Nat.max_eq_left (by omega : 0+base.steps+1≤cap)] using bound

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricTop
