import Proof.CaseAnalysis.RowsRawPairSeekBody

/-! One original occurrence block selects its X/C pair in the actual pooled
cache. The same index delimiter drives the loop, including empty entries;
only original logical cache bytes are scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsRawAtomSeek (heads data advance advance_run)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 2 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 2→ℕ:=![1,10]
noncomputable def programs : (i : Fin 2)→Machine 2 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>body
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 2→Bool) : Option (Fin 2):=
  if i=0 then if bits 0 then some 1 else none else some 0
noncomputable def loop:=RecoveryCalls.machine sizes programs 0 next
noncomputable def machine:=Composition.machine (Composition.machine advance loop) advance

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairSeek
