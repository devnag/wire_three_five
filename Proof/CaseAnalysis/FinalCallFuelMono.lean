import Proof.CaseAnalysis.FinalSupplierCall

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CallFuelMono

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1  `CallsReady` is monotone in its fuel -/

/-! ## §2  `callFuel` is monotone in `clauseBits` -/

/-! ## §3  The consequence that discharges `hcalls` -/


end NearCubicWires.RepairSource.CloseoutFinal.C10CallFuelMono
