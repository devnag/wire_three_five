import Proof.Assembly.FixedCore
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierTouching
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierRadix
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open scoped BigOperators

namespace PCJ9eff70d512234a4c_Fixed
namespace LiveRows
noncomputable section

def bound {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) : Nat :=
  touchingCost (occurrenceSupport occ) I
abbrev Seed {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : Nat) :=
  MargulisWalkSample (2 ^ toeplitzWalkSideBits (canonicalGradedRank occ.length (bound occ I)))
    (canonicalWalkLength den)

def coordinatePoly {q : Nat} (normalized : Bool)
    (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : Nat)
    (mask : Finset (Fin occ.length)) (sample : Seed occ I den)
    (candidate : Fin (occ.length + 1)) : StructuralGF2Polynomial :=
  let compile := if normalized then Normalized.structuralMaskedWalkListCoordinate
    else CanonicalFourfoldRowProgram.structuralMaskedWalkListCoordinate
  compile mask (canonicalGradedLabel occ.length (bound occ I))
    (executableGradedWindow (depth := canonicalGradedDepth (bound occ I)) (bound occ I))
    gradedTerminalWindow sample candidate

def constantCount {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q))
    (x : BitInput q) (mask : Finset (Fin occ.length)) : Nat :=
  ∑ i ∈ mask, (occurrenceResidualConstant occ I x i).toNat

def modularOffset {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q))
    (x : BitInput q) (e : LabelledEquation (Fin occ.length)) (p : Nat) : Nat :=
  (((∑ i, e.weights i * ((occurrenceResidualConstant occ I x i).toNat : Int)) - e.target) % (p : Int)).toNat

def symPolynomial (normalized : Bool) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (den : Nat) (sample : Seed (symmetricFourfoldOccurrences r) I den)
    (offset : Fin r.circuits.length → Nat) : StructuralGF2Polynomial :=
  let conjunction := if normalized then Normalized.structuralGF2FiniteConjunction
    else CanonicalFourfoldRowProgram.structuralGF2FiniteConjunction
  let lookup := if normalized then Normalized.structuralGF2OneHotLookup
    else CanonicalFourfoldRowProgram.structuralGF2OneHotLookup
  conjunction (fun i : Fin r.circuits.length =>
    lookup (shiftedFiniteLookup (offset i) (symmetricCircuitTopLookup r i))
      (coordinatePoly normalized (symmetricFourfoldOccurrences r) I den
        (symmetricCircuitMask r i) sample))

def thrPolynomial (normalized : Bool) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (I : Finset (Fin r.q)) (den : Nat) (sel : ThresholdRows.Selection a r)
    (p offset : Nat) (sample : Seed (thresholdFourfoldOccurrences r) I den) : StructuralGF2Polynomial :=
  let tupleRow := if normalized then
    Normalized.structuralGF2ModularRadixRow (digits := modulusDigitCount p)
    else CanonicalFourfoldRowProgram.structuralGF2ModularRadixRow (digits := modulusDigitCount p)
  tupleRow p offset 2
    (fun digit candidate => coordinatePoly normalized (thresholdFourfoldOccurrences r) I den
      (Finset.univ.filter (fun i =>
        (modularCoefficientResidue (ThresholdRows.equation a r sel) p i).testBit digit.val))
      sample candidate)

def residualAssignment {q : Nat} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q))
    (x : BitInput q) : Nat → Bool :=
  encodedFiniteBooleanAssignment (occurrenceResidualVariable occ I x)

def symOffsets (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (x : BitInput r.q) : Fin r.circuits.length → Nat :=
  fun i => constantCount (symmetricFourfoldOccurrences r) I x (symmetricCircuitMask r i)

end
end LiveRows
end PCJ9eff70d512234a4c_Fixed
