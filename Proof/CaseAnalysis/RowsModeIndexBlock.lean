import Proof.PCP.ProjectionNormalizationUnaryCore
import Proof.CaseAnalysis.RowsModeParity
import Proof.MachineModel.Encoding

/-! A real binary tuple/literal index emits its exact ordinary raw index
block. The existing predecessor loop appends the unary marks and consumes
the private binary copy; original tuple/cache tapes remain outside it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeIndexBlock
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RadixSemantics SignedSortKey
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (bit : Bool) : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then
    some ⟨1,![none,none,none,some bit],![.stay,.stay,.stay,.right]⟩ else none

noncomputable def machine:=Composition.machine (Composition.machine (mark true) UnaryCore.machine) (mark false)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeIndexBlock
