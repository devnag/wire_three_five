import Proof.CaseAnalysis.FinalCallCountMajorant

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountCap

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The monomial count of the polynomial algebra -/

variable {Atom : Type}

@[simp] theorem constant_length (d : ℕ) (c : ℚ) :
    (CircuitPolynomial.constant (Circuit := Atom) d c).monomials.length = 1 := rfl

@[simp] theorem atom_length (a : Atom) : (atomPolynomial a).monomials.length = 1 := rfl

/-! ## §2 The site majorant -/

/-! ## §3 The clause-address loop -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountCap
