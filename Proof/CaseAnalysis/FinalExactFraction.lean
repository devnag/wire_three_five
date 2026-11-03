import Proof.CaseAnalysis.FinalStageWidths
import Proof.CaseAnalysis.FinalSupplierAccuracy

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 An arbitrary per-record stream -/

/-- **The phase's record stream, at an arbitrary per-record denominator.**  Same
shape as `phaseRecords` (`Proof/CaseAnalysis/FinalWorkerDockSeam.lean`) -- the
concatenation over PCPP clause addresses of one record per monomial -- except
that the record is an arbitrary function of the address AND the monomial, so each
record carries its own `denominator` field. -/
noncomputable def phaseRecords' {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) : List Entry :=
  (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
    (fun address =>
      (siteCalls phase pcpp coordinate systematicAtom address).monomials.map (record address))

/-! ## §2 The exact-fraction record, and that its denominators may genuinely differ -/

/-- **A.13.9's record shape.**  Numerator and denominator are arbitrary functions
of the address and the monomial; the only constraint is the one `Calls` names. -/
def exactFractionRecord {Atom : Type} (clauseAddresses : ℕ)
    (num den : Fin clauseAddresses → CircuitMonomial Atom 4 → ℕ)
    (address : Fin clauseAddresses) (monomial : CircuitMonomial Atom 4) : Entry :=
  ⟨coefficientEstimate monomial.coefficient, num address monomial, den address monomial⟩

/-! ## §3 The three consumer applications, at the actual list type and width formula -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe
