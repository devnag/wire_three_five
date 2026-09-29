import Proof.MachineModel.RuntimeShape
import Proof.SourceAssembly.SourceRequestSymOriginal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule
open NearCubicWires.RecoveryWitnessPolicy NearCubicWires.SupplierEstimator
open NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.SupplierPipeline

/-! ## 1. The table factor beats every fixed polynomial past a live-scale onset -/

/-! ## 2. The two code widths are polynomial in the description cap -/

theorem encNat_poly : PolynomiallyBounded encodeNatBitsBound := by
  unfold encodeNatBitsBound
  exact polynomiallyBounded_add (polynomiallyBounded_constant 1) <|
    polynomiallyBounded_mul
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2)
        (polynomiallyBounded_pow polynomiallyBounded_id 4))
      (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))

theorem natCode_poly : PolynomiallyBounded canonicalNatCodeBitBound := by
  change PolynomiallyBounded (fun p => canonicalNatCodeBitBound p)
  simpa only [canonicalNatCodeBitBound] using
    polynomiallyBounded_comp encNat_poly (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))

theorem intCode_poly : PolynomiallyBounded canonicalIntCodeBitBound := by
  change PolynomiallyBounded (fun p => canonicalIntCodeBitBound p)
  simpa only [canonicalIntCodeBitBound] using
    polynomiallyBounded_mul (polynomiallyBounded_constant 2)
      (polynomiallyBounded_add (polynomiallyBounded_constant 1) encNat_poly)

theorem balancedCode_poly {atom : ℕ → ℕ} (h : PolynomiallyBounded atom) :
    PolynomiallyBounded (fun p => canonicalBalancedCodeBitBound p (atom p)) := by
  have hprod := polynomiallyBounded_mul
    (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_pow polynomiallyBounded_id 4))
    (polynomiallyBounded_add (polynomiallyBounded_mul polynomiallyBounded_id h) (polynomiallyBounded_constant 1))
  simpa only [canonicalBalancedCodeBitBound] using polynomiallyBounded_add (polynomiallyBounded_constant 1) hprod

theorem tagged3_poly {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun p => taggedListBitBound [f p, g p, h p]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have t3 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hh hone)
  have t2 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hg t3)
  simpa only [taggedListBitBound] using polynomiallyBounded_mul hfour (polynomiallyBounded_add hf t2)

theorem tagged4_poly {f g h k : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) (hk : PolynomiallyBounded k) :
    PolynomiallyBounded (fun p => taggedListBitBound [f p, g p, h p, k p]) := by
  have hone := polynomiallyBounded_constant 1
  have hfour := polynomiallyBounded_constant 4
  have t4 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hk hone)
  have t3 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hh t4)
  have t2 := polynomiallyBounded_mul hfour (polynomiallyBounded_add hg t3)
  simpa only [taggedListBitBound] using polynomiallyBounded_mul hfour (polynomiallyBounded_add hf t2)

theorem gateCode_poly : PolynomiallyBounded canonicalSupportedGateCodeBitBound := by
  change PolynomiallyBounded (fun p => canonicalSupportedGateCodeBitBound p)
  simpa only [canonicalSupportedGateCodeBitBound] using
    tagged3_poly (balancedCode_poly intCode_poly) intCode_poly (balancedCode_poly (polynomiallyBounded_constant 1))

/-- The THR admission width `ThrSwitch.codeWidth` is polynomial. -/
theorem thrWidth_poly : PolynomiallyBounded SourceRequest.ThrSwitch.codeWidth := by
  change PolynomiallyBounded (fun p => canonicalThresholdCircuitCodeBitBound p)
  simpa only [canonicalThresholdCircuitCodeBitBound] using
    tagged4_poly natCode_poly natCode_poly (balancedCode_poly gateCode_poly) gateCode_poly

/-- The SYM admission width `SymOriginal.symCodeWidth` is polynomial. -/
theorem symWidth_poly : PolynomiallyBounded SourceRequest.SymOriginal.symCodeWidth := by
  change PolynomiallyBounded (fun p => canonicalSymmetricCircuitCodeBitBound p)
  simpa only [canonicalSymmetricCircuitCodeBitBound] using
    tagged4_poly natCode_poly natCode_poly (balancedCode_poly gateCode_poly)
      (balancedCode_poly (polynomiallyBounded_constant 1))

/-! ## 3. The caps at the intended instantiation, and the window -/

/-! ## 4. At the consumers' exact quantities -/

end NearCubicWires.SourceBudget

