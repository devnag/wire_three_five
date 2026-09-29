import Proof.CaseAnalysis.FinalSupplierCall

namespace NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1  The record prefixes saturate at the branch's own address count -/

/-! ## §2  The call loop at a FREE round count -/

/-! ## §3  The same, as S0's `CallsReady` -/

/-! ## §4  The deliverable: the counter at the paper's envelope -/


end NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter
