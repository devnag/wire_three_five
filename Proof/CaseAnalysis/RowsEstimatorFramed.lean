import Proof.CaseAnalysis.RowsEstimatorPrepare

/-! The actual emitted cut stream and raw retained d,p,odd fields now reach
EquationRowRaw's exact framed source. No G or length driver is input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Framed
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 59) : Fin 68:=
  if h:j.val<55 then ⟨j.val,by omega⟩ else ⟨j.val+9,by omega⟩
theorem injective : Function.Injective slots:=by
  intro i j he
  have h:=congrArg Fin.val he
  simp only [slots] at h
  split_ifs at h <;> dsimp at h <;> apply Fin.ext <;> omega

def extend (A : Fin 64→List Bool) : Fin 68→List Bool:=
  fun i=>Fin.addCases (m:=64) (n:=4) (motive:=fun _=>List Bool) A (fun _=>[]) i
def input (row : EquationRow.Input):=extend (Prepare.input row)
noncomputable def first:=TapeEmbedding.machine 4 Prepare.machine
noncomputable def last:=RecoveryFocus.machine slots Header.framed
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input):=Prepare.budget row+1+Header.framedBudget row

theorem projected_input (row : EquationRow.Input) (j : Fin 59) :
    extend (Prepare.output row) (slots j)=Header.framedInput row j:=by
  by_cases hj:j.val<55
  · let i : Fin 55:=⟨j.val,hj⟩
    change extend (Prepare.output row) (slots (((i.castAdd 1).castAdd 1).castAdd 2))=
      Header.framedInput row (((i.castAdd 1).castAdd 1).castAdd 2)
    have hs:slots (((i.castAdd 1).castAdd 1).castAdd 2)=(i.castAdd 9).castAdd 4:=by
      apply Fin.ext
      simp [slots,i.isLt]
    rw [hs]
    simp only [extend,Fin.addCases_left,Header.framedInput,AppendOutputFrame.input,
      AppendOutputLength.input]
    exact Prepare.header_input row i
  · have hv : j.val=55 ∨ j.val=56 ∨ j.val=57 ∨ j.val=58:=by omega
    rcases hv with h | h | h | h
    · have he:j=55:=Fin.ext h
      rw [he];rfl
    · have he:j=56:=Fin.ext h
      rw [he];rfl
    · have he:j=57:=Fin.ext h
      rw [he];rfl
    · have he:j=58:=Fin.ext h
      rw [he];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Framed
