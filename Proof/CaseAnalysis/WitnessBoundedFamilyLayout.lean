import Proof.CaseAnalysis.WitnessHeaderSwitch
import Proof.CaseAnalysis.WitnessBoundedFields

/-! One actual mode-tag witness prefix. Its two cold-family programs
share the original input/header payloads and the same fresh verdict tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def exponent (sym : Bool):=if sym then 5 else 9
def denominator (sym : Bool) (symDen thrDen : ℕ):=if sym then symDen else thrDen
def localTapes (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool):=
  ColdFamily.base source a k D G (exponent sym)+FamilyCapacity.Call.extra E+FamilyCold.Call.extra
def workspace (a : PointwisePCPPAlgorithm) (k D G E : ℕ):=
  localTapes source a k D G E true+localTapes source a k D G E false
def offset (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool):=
  if sym then 0 else localTapes source a k D G E true
theorem segment (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) :
    offset source a k D G E sym+localTapes source a k D G E sym ≤ workspace source a k D G E:=by
  cases sym <;> dsimp only [offset,workspace] <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega

def verdictIndex (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool):=
  ColdFamily.base source a k D G (exponent sym)+FamilyCapacity.Call.extra E+724
def slots (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool):=
  HeaderDock.slots (workspace source a k D G E) (offset source a k D G E sym)
    (ColdInput.oracleIndex source k) (ColdLegal.tapes source a k D G (exponent sym))
    (verdictIndex source a k D G E sym) (segment source a k D G E sym)

def first (a : PointwisePCPPAlgorithm) (k D G E : ℕ):=
  TapeEmbedding.machine (workspace source a k D G E+1) CompetitorWitnessBounded.machine
def headerValid (x bits : List Bool) : Bool:=by
  classical
  exact decide (16*bits.length ≤ x.length ∧ CompetitorWitnessTriple.headerValid bits)
def passed (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad:k+3 ≤ Cpad):=
  let sym:=BoundedFields.symmetric bits
  headerValid (List.ofFn x) bits && ColdFamily.passed source a k CH Cpad cutoff D G copies (exponent sym)
    (denominator sym symDen thrDen) delta code sym x (BoundedFields.oracle bits) (BoundedFields.family bits) hpad

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamily
