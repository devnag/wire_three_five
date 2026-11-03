import Proof.SourceAssembly.SourceRequestSelBackMaps

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelBack
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

section
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- A fixed port of the local universe. -/
def up {t : Nat} (z : Fin NF) : Fin (NF + (19 + 4 * t)) := Fin.castAdd _ z

end

/-! ## The site list's length and the record of every call -/

section slots

end slots

section four
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- The THR producer at the admission caps. -/
abbrev PT (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat) := ThrSwitch.producer (pcpp := pcpp) da Pw W Ld

end four

section back

end back

end
end NearCubicWires.SourceRequest.SelBack
