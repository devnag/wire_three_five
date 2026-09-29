import Proof.CaseAnalysis.CloseoutWitnessColdFamilyLayout

/-! The whole cold family keeps the exact original family output layout.
This predicate is merely its retained streams/store, not a supplied worker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization CanonicalWitnessCodec
open CompetitorSumFold CompetitorSumWidth RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def scale (a : PointwisePCPPAlgorithm) (G D copies : ℕ) (delta : ℚ) (n : ℕ):=
  FamilyResources.sourceScale a source.coefficient source.degrees.queries G D delta copies n
def familyFlag (a : PointwisePCPPAlgorithm) (k CH Cpad D copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad : k+3≤Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  let r:=ColdNative.request source a k CH Cpad code x hpad oracle
  let cb:=(a.output r).clauseBits
  let W:=LegalPolicy.W e den r.arity
  FamilyCold.passed sym ((a.output r).systematicBits+(a.output r).auxiliaryBits)
    (FamilyResources.coefficientCap delta copies D r.arity cb) (FamilyResources.termCap delta copies D r.arity cb)
    r.arity W (DescriptionPolicy.value sym r.arity (CorePolicy.q0 D r.arity) W)
    (CloseoutSampledWitness.massCap delta copies) bits (SignedSortKey.binary (natBitLength r.arity) r.arity)
def passed (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e den : ℕ) (delta : ℚ)
    (code : List Bool) (sym : Bool) {n : ℕ} (x : BitInput n) (raw bits : List Bool) (hpad : k+3≤Cpad):=
  ColdNative.passed source k CH Cpad cutoff G code (List.ofFn x) raw &&
    (decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)).any
      (familyFlag source a k CH Cpad D copies e den delta code sym x bits hpad)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
