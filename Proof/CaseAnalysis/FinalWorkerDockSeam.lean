import Proof.CaseAnalysis.FinalWorkerDockBody

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **The phase's whole call stream**: the concatenation, over PCPP clause
addresses, of the per-address record lists of S1.  This is the list the
clause-address driver accumulates and the multiply stage reads. -/
noncomputable def phaseRecords {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) : List Entry :=
  (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
