import Proof.CaseAnalysis.WitnessMass
import Proof.CaseAnalysis.WitnessTermMass

/-! Retain one checked coefficient before clearing its parser. The record
uses one sign bit and the same two guarded b-bit fields. Only the logical
output cursor advances; neither allocated padding nor old prefixes are scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientRecord
open LocalBitMultitape RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


noncomputable def literal (bits : List Bool):=
  RecoveryFocus.machine (fun _ : Fin 1=>(3 : Fin 5)) (HierarchyFixedWord.raw bits)
noncomputable def sign:=TapeEmbedding.machine 1 CloseoutRowsSignedAppend.sign
noncomputable def field (i : Fin 2):=CompetitorFieldEmit.program (if i.val=0 then 1 else 2) (3 : Fin 5) 4
noncomputable def first:=Composition.machine (literal [true]) sign
noncomputable def signed:=Composition.machine first (literal [false])
noncomputable def numerator:=Composition.machine signed (field 0)
noncomputable def machine:=Composition.machine numerator (field 1)


end NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientRecord
