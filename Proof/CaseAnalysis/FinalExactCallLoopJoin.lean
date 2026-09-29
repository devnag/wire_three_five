import Proof.CaseAnalysis.FinalStageJoin

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactCallLoopJoin

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule (clauseBitsSchedule widthAt)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank callFuel callMachine)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

section Abstract

end Abstract

/-! ## §2 The same at the exact-fraction record family and the paper's own envelope -/

section Primed

/-! ## §3 `CallsReady` from the bounded family, the idle round, and the prologue -/

end Primed

section Stage

/-! ## §5 `hfit` is not open: it is `clauseBits_le_schedule`, up to ONE onset

`clauseBits_le_schedule`
(`Proof/CaseAnalysis/FinalClauseBitsUniform.lean`) already proves `hfit` at
`paper.tex:4516`'s own schedule, from `Parameters.clauses`
(`Proof/CaseAnalysis/FinalResidualLeaves.lean`) alone.  What it carries and
`hcalls` does not is an ONSET: `hcalls`'s guard is
`Soundness.cutoff (constantsOf sources)`.  The gap between the two is named here
and NOT smuggled -- it is the same gap `stage_field_hfuel`'s and
`stageReady_at_polyFuel`'s `hfit` carry (`Proof/CaseAnalysis/FinalClauseBitsUniform.lean`
§8), so it is SHARED, not new. -/

/-! ## §6 The plug, TYPE-CHECKED rather than transcribed -/

end Stage

end


end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactCallLoopJoin
