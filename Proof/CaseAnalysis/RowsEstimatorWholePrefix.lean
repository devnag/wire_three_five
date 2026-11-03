import Proof.CaseAnalysis.RowsEstimatorBudget

/-! Dock the actual cold native-stream prefix directly into the existing
raw-row estimator bank. Every non-source metadata word remains explicit;
only the original source frame is produced by this paid prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholePrefix
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program):=70+CloseoutRowsRawRecord.tapes p
def slots (p : Program) (i : Fin (CloseoutRowsRawRecord.tapes p)) : Fin (tapes p):=
  if i.val=0 then ⟨66,by unfold tapes;omega⟩ else i.natAdd 70

theorem injective (p : Program) : Function.Injective (slots p):=by
  intro i j he
  have hv:=congrArg Fin.val he
  simp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> apply Fin.ext <;> omega

def extra (p : Program) (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool)
    (i : Fin (CloseoutRowsRawRecord.tapes p)):=if i.val=0 then [] else data i
def input (p : Program) (row : EquationRow.Input) (C : ℕ)
    (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool):=
  fun i=>Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (motive:=fun _=>List Bool)
    (Cold.input row C) (extra p data) i
def heads (p : Program) (row : EquationRow.Input):=
  fun i=>Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (motive:=fun _=>ℕ)
    (Cold.heads row) (fun _=>0) i
noncomputable def first (p : Program):=TapeEmbedding.machine (CloseoutRowsRawRecord.tapes p) Cold.machine
noncomputable def last {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s):=
  RecoveryFocus.machine (slots p) callee
noncomputable def machine {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s):=
  Composition.machine (first p) (last p callee)
noncomputable def entry {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s)
    (row : EquationRow.Input) (C : ℕ) (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool):=
  (⟨(machine p callee).start,heads p row,input p row C data⟩ : Configuration (tapes p) _)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholePrefix
