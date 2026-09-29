import Proof.CaseAnalysis.RowsEstimatorReset

/-! One reusable estimator bank, with native source/C protected, an external
growing scalar stream, and a separately paid D driver and reset log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program):=WholePrefix.tapes p+1+2
def old (p : Program) (i : Fin (WholePrefix.tapes p)) : Fin (tapes p):=(i.castAdd 1).castAdd 2
def log (p : Program) : Fin (tapes p):=((0 : Fin 1).natAdd (WholePrefix.tapes p)).castAdd 2
def output (p : Program) : Fin (tapes p):=(0 : Fin 2).natAdd (WholePrefix.tapes p+1)
def driver (p : Program) : Fin (tapes p):=(1 : Fin 2).natAdd (WholePrefix.tapes p+1)
def copySlots (p : Program) : Fin 3→Fin (tapes p):=![old p (Whole.recordSlot p),output p,log p]

def work (p : Program) (i : Fin (WholePrefix.tapes p-2)) : Fin (tapes p):=
  if i.val<52 then ⟨i.val,by unfold tapes WholePrefix.tapes;omega⟩
  else if i.val<67 then ⟨i.val+1,by unfold tapes WholePrefix.tapes;omega⟩
  else ⟨i.val+2,by have h:=i.isLt;unfold tapes WholePrefix.tapes at *;omega⟩

def eraseSlots (p : Program) : Fin (WholePrefix.tapes p-2+1+1)→Fin (tapes p):=
  Fin.addCases (Fin.addCases (work p) (fun _ : Fin 1=>driver p)) (fun _ : Fin 1=>log p)

noncomputable def erase (p : Program):=RecoveryFocus.machine (eraseSlots p)
  (RecoveryScratchErase.resetMachine (WholePrefix.tapes p-2))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
