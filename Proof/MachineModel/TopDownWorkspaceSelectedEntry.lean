import Proof.MachineModel.TopDownWorkspaceSelectedOriginals
import Proof.CaseAnalysis.FinalEngineFuelSeam

/-! Direct reuse of the actual width/count prologue after selected admission.
The old parser bank is retained; only the original input, witness and true
length flag are aliased. All prologue work occurs in the selected fresh bank.
The prologue produces its envelope count, not the original PCPP clause count.
Its semantic width schedule uses PolynomialClock.ordinaryClock k. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntry
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.ProjectionNormalization
open WorkspaceGuardedWorker (entry reference)
open WorkspaceSelectedAdmission (originalTapes preFuel coldCutoff)
open RecoveryRootRound
noncomputable section

/-- The logical prologue prefix fits in the caller's fresh bank. Its three
public words are physically aliased; every other logical port is fresh. -/
def slots {t m extra : Nat} (ht : 2≤t) (hspace : m≤extra) (i : Fin m) :
    Fin (t+1+1+extra) :=
  ⟨if i.val=0 then 0 else if i.val=1 then 1 else if i.val=216 then t+1 else t+2+i.val,
    by have := i.isLt;split_ifs <;>omega⟩

def engineTapes (sources : EightSources) (k r D : Nat) : Nat :=
  CloseoutFinalC10SeedEngine.tapesOf
    (HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp sources) (CloseoutFinalC10SeedEngine.rq sources)) r D

def size (sources : EightSources) (k r D : Nat) : Nat := 218+(60+(engineTapes sources k r D+23))+1

def output (sources : EightSources) (k r D n : Nat) (x bits : List Bool) (w : Nat→List Bool) :
    Fin (size sources k r D) → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0)
      (List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true) x bits w)
    (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word
      (2^CloseoutLanguage.clauseWidth D (C10PartsSchedule.widthAt sources k n)))

def outputHeads (sources : EightSources) (k r D : Nat) : Fin (size sources k r D) → Nat :=
  Fin.addCases (motive:=fun _=>Nat) (fun _ =>0) (fun _ : Fin 1=>1)

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntry
