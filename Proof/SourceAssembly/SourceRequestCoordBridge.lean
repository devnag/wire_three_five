import Proof.SourceAssembly.SourceRequestTermReader
import Proof.SourceAssembly.SourceFactorSelModes
import Proof.Assembly.CappedCoordinate

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CoordBridge
open NearCubicWires CanonicalBinary CanonicalWitnessCodec SupplierPipeline ComponentwisePolynomial SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## The codec, inverted on the reader's words -/

/-! ## The interface the composition reads -/


section leaf

end leaf

end
end NearCubicWires.SourceRequest.CoordBridge

