import Proof.CaseAnalysis.FinalEnvelopeCounter
import Proof.CaseAnalysis.FinalUnaryExpDock

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform

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

/-! ## §1 The prologue's target bank is branch-free -/

/-! ## §2 The obligation, with the length INSIDE the machine binder -/

/-! ## §3 One run of the prologue is `hpre` at EVERY branch -/

/-! ## §4 The consumer: `CallsReady`, from `Prologue` and the emitter -/

/-! ## §6 Two readings of the bank, and the count word built -/

/-! ## §7 The head bump on the loop's counter tape -/

/-! ## §8 The residual, named: two length-driven unary words -/

/-! ## §8b `Seed` needs no new machine in the bank's ABI: the dock bridge -/

/-! ## §9 `Seed` is the ONLY residual: the prologue, assembled -/

end NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform
