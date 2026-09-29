import Proof.CaseAnalysis.RowsCircuitResourceBounds

/-! The full circuit starts with the original raw field and paid policy
words. One actual C-sweep allocates all reusable gate scratch and retained
top targets. Domain, caps and empty append streams are preserved. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAllocate
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def gate (i : Fin 1048) : Fin 1703:=⟨639+(CloseoutRowsCircuitBottom.scratchSlots i).val,by
  have h:=CloseoutRowsCircuitBottom.scratch_small i;omega⟩
def extra : Fin 6→Fin 1703:=![1691,1692,1696,1697,1701,1702]
def scratch : Fin 1054→Fin 1703:=Fin.addCases (m:=1048) (n:=6) gate extra
def slots : Fin 1056→Fin 1703:=Fin.addCases (m:=1054) (n:=2) scratch ![1694,1695]
noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1054)

theorem scratch_old (i : Fin 1048) : scratch (i.castAdd 6)=gate i:=by
  simp only [scratch,Fin.addCases_left]
theorem scratch_new (i : Fin 6) : scratch (i.natAdd 1048)=extra i:=by
  simp only [scratch,Fin.addCases_right]
theorem slots_old (i : Fin 1054) : slots (i.castAdd 2)=scratch i:=by
  simp only [slots,Fin.addCases_left]
theorem slots_new (i : Fin 2) : slots (i.natAdd 1054)=(![1694,1695] : Fin 2→Fin 1703) i:=by
  simp only [slots,Fin.addCases_right]

theorem gate_val (i : Fin 1048) : (gate i).val=639+(if i.val<1035 then i.val else i.val+1):=by
  exact congrArg (fun n=>639+n) (CloseoutRowsCircuitBottom.scratch_val i)
theorem gate_injective : Function.Injective gate:=by
  intro i j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  rw [gate_val,gate_val] at hv
  apply Fin.ext;split_ifs at hv <;> omega
theorem gate_range (i : Fin 1048) : 639 ≤ (gate i).val ∧ (gate i).val ≤ 1687 ∧ (gate i).val≠1674:=by
  rw [gate_val];split_ifs <;> omega
theorem extra_range (i : Fin 6) : 1691 ≤ (extra i).val ∧ (extra i).val≠1694 ∧
    (extra i).val≠1695 ∧ (extra i).val≠1698 ∧ (extra i).val≠1699:=by
  fin_cases i <;> decide
theorem scratch_injective : Function.Injective scratch:=by
  intro i j h
  revert h
  refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ i
  · intro a
    refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ j
    · intro b h;rw [scratch_old,scratch_old] at h
      exact congrArg (fun k : Fin 1048=>k.castAdd 6) (gate_injective h)
    · intro b h;rw [scratch_old,scratch_new] at h
      have hv:=congrArg (fun k : Fin 1703=>k.val) h
      have ga:=gate_range a;have eb:=extra_range b
      change (gate a).val=(extra b).val at hv;omega
  · intro a
    refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ j
    · intro b h;rw [scratch_new,scratch_old] at h
      have hv:=congrArg (fun k : Fin 1703=>k.val) h
      have ea:=extra_range a;have gb:=gate_range b
      change (extra a).val=(gate b).val at hv;omega
    · intro b h;rw [scratch_new,scratch_new] at h
      exact congrArg (fun k : Fin 6=>k.natAdd 1048) ((by decide : Function.Injective extra) h)
theorem scratch_range (i : Fin 1054) : 639 ≤ (scratch i).val ∧ (scratch i).val≠1674 ∧
    (scratch i).val≠1694 ∧ (scratch i).val≠1695 ∧
    (scratch i).val≠1698 ∧ (scratch i).val≠1699:=by
  refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ i
  · intro j
    rw [scratch_old]
    have h:=gate_range j;omega
  · intro j
    rw [scratch_new]
    have h:=extra_range j;omega
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  revert h
  refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ i
  · intro a
    refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ j
    · intro b h;rw [slots_old,slots_old] at h
      exact congrArg (fun k : Fin 1054=>k.castAdd 2) (scratch_injective h)
    · intro b h;rw [slots_old,slots_new] at h
      have hv:=congrArg (fun k : Fin 1703=>k.val) h
      have hs:=scratch_range a
      fin_cases b
      · change (scratch a).val=1694 at hv;omega
      · change (scratch a).val=1695 at hv;omega
  · intro a
    refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ j
    · intro b h;rw [slots_new,slots_old] at h
      have hv:=congrArg (fun k : Fin 1703=>k.val) h
      have hs:=scratch_range b
      fin_cases a
      · change 1694=(scratch b).val at hv;omega
      · change 1695=(scratch b).val at hv;omega
    · intro b h;rw [slots_new,slots_new] at h
      exact congrArg (fun k : Fin 2=>k.natAdd 1054) ((by decide : Function.Injective (![1694,1695] : Fin 2→Fin 1703)) h)
theorem prefix_outside (i : Fin 639) : ∀ j,slots j≠prefixSlots i:=by
  intro j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
  revert hv
  refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ j
  · intro a hv
    rw [slots_old] at hv
    have hs:=scratch_range a
    change (scratch a).val=i.val at hv;omega
  · intro a hv;rw [slots_new] at hv
    fin_cases a
    · change 1694=i.val at hv;omega
    · change 1695=i.val at hv;omega


end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitAllocate
