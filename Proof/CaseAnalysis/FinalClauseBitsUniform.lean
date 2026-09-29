import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalStageFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ClauseBitsUniform

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CompetitorRationalGap (zeta)
open NearCubicWires.RepairSource.CloseoutLanguage (selectedPCPP clauseWidth)
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer fixedProjection)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The native width, and the only side condition the cap carries -/

/-! ## §2 The cap, and the two facts it gives -/

/-! ## §3 The decoded family's limits, read off at a length-only argument -/

/-! ## §4 The two floors, both functions of the input length -/

/-! ## §5 The three premises -/

/-! ## §6 `hfuel`'s coordinate-degree cap -- the same quantity, third use -/

/-! ## §7 `hfuel`'s call cap, and the field -/

/-! ## §8 The same quantity at a THIRD field: `hstage`'s `hfit`

`stageReady_at_polyFuel` (`Proof/CaseAnalysis/FinalFuelRepin.lean`) -- the
premise card's producer for `StageBlock.hstage` -- carries
`hfit : (pcppOf …).clauseBits ≤ clauseBitsSchedule sources k p.clauseDegree n`
(`:598`) and an `hL` of exactly §6's shape (`:596`).  So the `clauseBits`
uniformity gates THREE of the fourteen fields, not two.

`pcppOf_clause_degree` (`Proof/CaseAnalysis/FinalOracleSizeBound.lean`) does
NOT serve this one: it EXHIBITS its own `degree`, while `hfit` is pinned at
`p.clauseDegree`.  The producer at that degree is `Parameters.clauses`
(`Proof/CaseAnalysis/FinalResidualLeaves.lean`), which is a FIELD -- free at
every consumer holding `p` -- and `ClauseReady`
(`Proof/CaseAnalysis/HardnessPremises.lean`) quantifies over EVERY length and
EVERY input, not only dyadic ones.  Unlike §2 this one carries an onset, which
`hstage` can afford because its field type is guarded by `Soundness.cutoff`. -/

end


end NearCubicWires.RepairOrdinary.CloseoutFinalC10ClauseBitsUniform
