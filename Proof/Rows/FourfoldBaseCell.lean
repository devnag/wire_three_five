import Proof.Rows.DigitBaseRun

/-! Four retained binary selection digits share the real per-circuit base
worker. All fixed circuit cursors and the decoded count remain resident. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
set_option maxErrors 4
namespace PCJ45bee56da9f34d5a_FourfoldBaseCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open SignedSortKey
noncomputable section

def extras (digits : Fin 4→Nat) (N v U : Nat):Fin 10→List Bool:=
  ![List.replicate v true,frame (binary v (digits 0)),frame (binary v (digits 1)),
    frame (binary v (digits 2)),frame (binary v (digits 3)),
    ZeroPadding.pad U (CompareMachine.word 0),ZeroPadding.pad U (CompareMachine.word 1),
    ZeroPadding.pad U (CompareMachine.word 2),ZeroPadding.pad U (CompareMachine.word 3),
    ZeroPadding.pad U (UnaryTemplate.tape N)]
def bank (source : List Bool) (digits : Fin 4→Nat) (N v w C U a : Nat):Fin 82→List Bool:=
  Fin.addCases (m:=72) (n:=10) (motive:=fun _=>List Bool)
    (fun i=>PCJ45bee56da9f34d5a_DigitBaseInput.bank source (List.replicate U false) 0 0 v w C U a (i.castAdd 3))
    (extras digits N v U)
def heads (pos : Nat) (i : Fin 82):=if i=81 then pos else if (77  ≤  i.val ∧ i.val < 81) then 1 else 0
def slots (j : Fin 4) (i : Fin 75):Fin 82:=
  if h:i.val<72 then ⟨i.val,by omega⟩ else if i=72 then ⟨77+j.val,by omega⟩
    else if i=73 then 72 else ⟨73+j.val,by omega⟩
theorem slots_injective (j : Fin 4):Function.Injective (slots j):=by fin_cases j <;>decide
def machine (j : Fin 4):=RecoveryFocus.machine (slots j) PCJ45bee56da9f34d5a_DigitBaseInput.machine

theorem head_slot (j : Fin 4) (pos : Nat) (i : Fin 75):
    heads pos (slots j i)=PCJ45bee56da9f34d5a_DigitBaseInput.heads 0 i:=by
  fin_cases j <;>fin_cases i <;>rfl

theorem bank_slot (j : Fin 4) (source : List Bool) (digits : Fin 4→Nat) (N v w C U a : Nat) (i : Fin 75):
    bank source digits N v w C U a (slots j i)=
      PCJ45bee56da9f34d5a_DigitBaseInput.bank source (List.replicate U false) j.val (digits j) v w C U a i:=by
  fin_cases j <;>fin_cases i <;>rfl

theorem outside_prefix (j : Fin 4) (i : Fin 82) (hi : ∀k,slots j k≠i):72 ≤ i.val:=by
  by_contra h
  have hlt:i.val<72:=by omega
  let k:Fin 75:=⟨i.val,by omega⟩
  apply hi k
  apply Fin.ext
  simp [slots,k,hlt]

theorem run (j : Fin 4) (digits : Fin 4→Nat) (pos : Nat) (words : List (List Bool)) (circuit : Fin words.length) (B : Nat) {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (v w C D U a : Nat)
    (hci : circuit.val=j.val) (hdigit : digits j=i.val)
    (hi : i.val<2^v) (hv : MatrixUnaryTemplate.budget v i.val<U)
    (hb : ∀x∈words,x.length ≤ B)
    (htop : PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit B+2 ≤ U)
    (hselected : words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    (hu : PCPPQueryNatural.budget n<U)
    (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length ≤ U)
    (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1 ≤ U)
    (hg : (exactWord (gs.get i)).length+2 ≤ U)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items (gs.get i),natBitLength x.1.natAbs ≤ w)
    (hc : 8*w+12 ≤ C) (hm : childMagnitude (gs.get i)<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items (gs.get i)) w C ≤ D)
    (hC : C+1 ≤ U) (hDU : D ≤ U) (ha : childMagnitude (gs.get i)+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget (gs.get i) w C+2 ≤ U)
    (hU : ∀ j,(PCJ45bee56da9f34d5a_SelectedBase.Base.words (ZeroPadding.pad U (exactWord (gs.get i))) (List.replicate (n+1) true)
      (n+1) w C U a j).length ≤ U) :
    Step (machine j) (PCJ45bee56da9f34d5a_DigitBaseRun.budget words circuit B gs i v w C U)
      (heads pos) (bank (words.flatMap frame) digits words.length v w C U a)
      (heads pos) (bank (words.flatMap frame) digits words.length v w C U (childMagnitude (gs.get i)+a)):=by
  have base:=PCJ45bee56da9f34d5a_DigitBaseRun.run words circuit B gs i v w C D U a hi hv hb htop hselected
    hu hp hf hg hw hc hm hD hC hDU ha hF hU
  rw [hci,←hdigit] at base
  have h:=base.dock (slots j) (slots_injective j) (heads pos)
    (bank (words.flatMap frame) digits words.length v w C U a)
    (head_slot j pos)
    (bank_slot j _ _ _ _ _ _ _ _)
  apply h.congr
  · exact dockH_existing _ _ _ (head_slot j pos)
  · apply HierarchyAllocation.install_eq (slots j) (slots_injective j)
    · exact bank_slot j _ _ _ _ _ _ _ _
    · intro k hk
      have hge:=outside_prefix j k hk
      let z:Fin 10:=⟨k.val-72,by omega⟩
      have hz:z.natAdd 72=k:=by
        apply Fin.ext
        change 72+(k.val-72)=k.val
        omega
      rw [←hz]
      simp only [bank,Fin.addCases_right]
end
end PCJ45bee56da9f34d5a_FourfoldBaseCell
