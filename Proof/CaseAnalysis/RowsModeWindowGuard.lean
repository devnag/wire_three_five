import Proof.CaseAnalysis.RowsModeShift

/-! Both window coefficients are computed by actual scalar scans. The
accumulator is initialized by a real write, and every scalar cursor returns. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (w degree target : Nat) : Fin 2→List Bool:=![frame (binary w degree),frame (binary w target)]
def data (w offset b scratch degree target C : Nat) (nonzero guard : Bool) : Fin 8→List Bool:=
  Fin.addCases (m:=6) (n:=2) (motive:=fun _=>List Bool)
    (CloseoutRowsModeShift.data w offset b scratch C nonzero guard) (extra w degree target)
def init : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun i=>if i=4 then some true else none,fun _=>.stay⟩ else none
def paritySlots : Fin 4→Fin 8:=![6,7,4,5]
noncomputable def parity:=RecoveryFocus.machine paritySlots CloseoutRowsModeParityReusable.machine
noncomputable def shift:=TapeEmbedding.machine 2 CloseoutRowsModeShift.machine
noncomputable def machine:=Composition.machine (Composition.machine init parity) shift

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowGuard
