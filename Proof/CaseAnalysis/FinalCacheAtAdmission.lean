import Proof.CaseAnalysis.WitnessBoundedFamilySupportRun

/-! Exact cache bytes exported from the existing original-input bounded run.
The proof recovers its selected child by determinism; the machine and budget
are unchanged, and no second source call is executed. Rejected inputs still
have the same total run and flag. Cache facts require its actual admission.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheAtAdmission

open NearCubicWires LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open ProjectionNormalization CloseoutWitness CanonicalWitnessCodec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

def cacheSlot (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) (j : Fin 19) :=
  BoundedFamilySupport.slots source a k D G E sym
    (ColdFamilySupport.cache source a k D G (BoundedFamily.exponent sym) E j)

/-- Exact cache facts on the physical parent tape map. -/
def Cached (a : PointwisePCPPAlgorithm) (k CH Cpad D G E : ℕ)
    (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool) (hpad : k + 3 ≤ Cpad)
    (heads : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E) + 1) → ℕ)
    (data : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E) + 1) → List Bool) : Prop :=
  ∃ oracle, decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
      (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle ∧
    oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G
      (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
    let r := ColdNative.request source a k CH Cpad code x hpad oracle
    ∀ j : Fin 19,
      data (cacheSlot source a k D G E (BoundedFields.symmetric bits) j) =
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j ∧
      heads (cacheSlot source a k D G E (BoundedFields.symmetric bits) j) = PCPPQueryClauseReuse.heads j


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheAtAdmission
