import Proof.MachineModel.TopDownSelectedAssembly
import Proof.MachineModel.CappedDecode
import Proof.CaseAnalysis.FinalSumFamilyTransport

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PCJd04de0277f804fcc_
open NearCubicWires NearCubicWires.CanonicalWitnessCodec NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.SelectedRecoveryIntegration NearCubicWires.SourceInterfaces

noncomputable section
variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
variable {gamma : Real} (p : Parameters sources gamma) (den : Nat)
variable {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)

def coordinate :
    Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle) →
      CircuitPolynomial (C10TotalDecode.Atom (pcppAt sources k clock x oracle)) 1 :=
  if CloseoutWitness.BoundedFields.symmetric bits then
    fun j => mapPolynomial C10TotalDecode.Atom.symmetric
      (familyCoordinate rfl (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) j)
  else
    fun j => mapPolynomial C10TotalDecode.Atom.threshold
      (familyCoordinate rfl (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) j)

theorem coordinate_sym (hs : CloseoutWitness.BoundedFields.symmetric bits = true)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    coordinate sources k clock p den x oracle bits j =
      mapPolynomial C10TotalDecode.Atom.symmetric
        (familyCoordinate rfl
          (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) j) := by
  unfold coordinate
  rw [if_pos hs]
  rfl

theorem coordinate_thr (hs : ¬ CloseoutWitness.BoundedFields.symmetric bits = true)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    coordinate sources k clock p den x oracle bits j =
      mapPolynomial C10TotalDecode.Atom.threshold
        (familyCoordinate rfl
          (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) j) := by
  unfold coordinate
  rw [if_neg hs]
  rfl

/-- `proofValueOf` on the symmetric branch, with no decoding hypothesis: the
total default is itself a `SumFamily.value`. -/
theorem proofValue_symmetric (hs : CloseoutWitness.BoundedFields.symmetric bits = true) :
    P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits =
      CloseoutWitness.SumFamily.value
        SupplierPipeline.NormalizedSymmetricThresholdCircuit.eval
        (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) := by
  unfold P1Independent.CappedDecode.proofValueOf
  rw [if_pos hs]

/-- `proofValueOf` on the threshold branch. -/
theorem proofValue_threshold
    (hs : ¬ CloseoutWitness.BoundedFields.symmetric bits = true) :
    P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits =
      CloseoutWitness.SumFamily.value
        SupplierPipeline.NormalizedThresholdThresholdCircuit.eval
        (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) := by
  unfold P1Independent.CappedDecode.proofValueOf
  rw [if_neg hs]

/-- **`hcoordinate`, at the decode union.**  The seam is met at the FIXED atom
type `C10TotalDecode.Atom`, the FIXED evaluation `C10TotalDecode.evaluate`, and
the FIXED proof value `P1Independent.CappedDecode.proofValueOf`. -/
theorem coordinateExpands_symmetric
    (hs : CloseoutWitness.BoundedFields.symmetric bits = true) :
    CoordinateExpands (pcppAt sources k clock x oracle) C10TotalDecode.evaluate
      (P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits)
      (coordinate sources k clock p den x oracle bits) := by
  intro input j
  rw [coordinate_sym sources k clock p den x oracle bits hs j,
    proofValue_symmetric sources k clock p den x oracle bits hs]
  exact coordinateExpands_map
    (Circuit := SupplierPipeline.NormalizedSymmetricThresholdCircuit)
    (wires := SupplierPipeline.NormalizedSymmetricThresholdCircuit.wireCount)
    (description := SupplierPipeline.NormalizedSymmetricThresholdCircuit.descriptionBits)
    (limits := P1Independent.CappedDecode.symLimits sources k clock p den x oracle)
    (Atom := C10TotalDecode.Atom (pcppAt sources k clock x oracle))
    (circuit := (req sources k clock x oracle).circuit)
    (pcppAt sources k clock x oracle)
    SupplierPipeline.NormalizedSymmetricThresholdCircuit.eval
    C10TotalDecode.evaluate C10TotalDecode.Atom.symmetric
    (fun atom point => evaluate_symmetric (pcppAt sources k clock x oracle) atom point)
    (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) input j

theorem coordinateExpands_threshold
    (hs : ¬ CloseoutWitness.BoundedFields.symmetric bits = true) :
    CoordinateExpands (pcppAt sources k clock x oracle) C10TotalDecode.evaluate
      (P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits)
      (coordinate sources k clock p den x oracle bits) := by
  intro input j
  rw [coordinate_thr sources k clock p den x oracle bits hs j,
    proofValue_threshold sources k clock p den x oracle bits hs]
  exact coordinateExpands_map
    (Circuit := SupplierPipeline.NormalizedThresholdThresholdCircuit)
    (wires := SupplierPipeline.NormalizedThresholdThresholdCircuit.wireCount)
    (description := SupplierPipeline.NormalizedThresholdThresholdCircuit.descriptionBits)
    (limits := P1Independent.CappedDecode.thrLimits sources k clock p den x oracle)
    (Atom := C10TotalDecode.Atom (pcppAt sources k clock x oracle))
    (circuit := (req sources k clock x oracle).circuit)
    (pcppAt sources k clock x oracle)
    SupplierPipeline.NormalizedThresholdThresholdCircuit.eval
    C10TotalDecode.evaluate C10TotalDecode.Atom.threshold
    (fun atom point => evaluate_threshold (pcppAt sources k clock x oracle) atom point)
    (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) input j

theorem coordinateExpands :
    CoordinateExpands (pcppAt sources k clock x oracle) C10TotalDecode.evaluate
      (P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits)
      (coordinate sources k clock p den x oracle bits) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · exact coordinateExpands_symmetric sources k clock p den x oracle bits hs
  · exact coordinateExpands_threshold sources k clock p den x oracle bits hs


end
end PCJd04de0277f804fcc_
