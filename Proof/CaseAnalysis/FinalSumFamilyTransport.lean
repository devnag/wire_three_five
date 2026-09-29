import Proof.CaseAnalysis.FinalExactnessFamily
import Proof.CaseAnalysis.FinalStageContracts

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 Relabelling the atoms of a canonical polynomial

`CircuitPolynomial Circuit degree` (`Proof/Circuits/ComponentwisePolynomial.lean`)
carries `Circuit : Type`, not a `CircuitFamily`, so a change of atom type along
any `F : Source → Target` is a pure list relabelling.  What has to be proved is
that it is semantics preserving; that is `mapPolynomial_value`. -/

/-! ## §2 The transport -/

/-! ## §3 The two decode embeddings, and their semantics -/

/-! ## §4 The decoded coordinate, at the decode union -/

noncomputable section


/-! ## §5 The two branch policies share the coefficient caps

`CloseoutSampledWitness.symmetricLimits` (`Proof/CaseAnalysis/SampledWitness.lean`)
and `thresholdLimits` (`Proof/CaseAnalysis/SampledWitness.lean`) differ only in `wireCap` and `descriptionCap`;
`expectedArity`, `termCap`, `coefficientBitCap` and `coefficientMassCap` are the
same `Average.limits` (`Proof/CaseAnalysis/WitnessAverage.lean`) arguments.  So a
single bound serves both branches, and `hcoefficients` / `hmass` need no case
split at the consumer. -/

/-! ## §6 The three `StageBlock` fields, in their verbatim shapes -/

end


end NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
