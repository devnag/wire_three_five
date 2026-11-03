import Proof.SourceAssembly.SourceNative
import Proof.SourceAssembly.SourceRequestFactorLoop

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RepairSource RepairSource.CloseoutFinal SupplierEstimator SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace NearCubicWires.SourceConstruction.TraceData
noncomputable section

section data
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))

abbrev order := SourceRequest.FactorLoop.monomials coordinate ph ci

/-- The coefficient of call `j`. -/
def coefficientOf (j : Nat) : CompetitorValidity.Estimate :=
  CloseoutFinalC10SupplierCalls.coefficientEstimate (((order coordinate ph ci).map (fun m => m.coefficient)).getD j 0)

variable (sources : EightSources) (L target : Nat) (mode : Bool)

/-- The call's fraction (`total`, `denominator`). -/
def fractionOf (j : Nat) : Nat × Nat :=
  LiveRows.fraction sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)

/-- The clause's entries, one per call in `order`. -/
def entriesOf : List CloseoutRowsEstimatorCoefficients.Stream.Entry :=
  List.ofFn (fun j : Fin (order coordinate ph ci).length =>
    (⟨coefficientOf coordinate ph ci j.val, (fractionOf coordinate ph ci sources L target mode j.val).1,
      (fractionOf coordinate ph ci sources L target mode j.val).2⟩ : CloseoutRowsEstimatorCoefficients.Stream.Entry))

variable (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)

/-- The layout family the admission supplies, one per call. -/
abbrev LayoutFamily := ∀ j : Nat,
  Packets.Layout (decompositionOf sources)
    (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))
    (Packets.geometry selector (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))

/-- Call `j`'s data list. -/
def dsOf (lay : LayoutFamily coordinate ph ci sources L target mode selector) (j : Nat) :
    List P1TopDownPaidReusable.Datum :=
  dataList (decompositionOf sources) (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))
    (Packets.geometry selector (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))
    (lay j) (compiler sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)
      (Packets.geometry selector (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))))

/-- Call `j`'s child-list word length `L_j`. -/
def lenOf (j : Nat) : Nat :=
  (exactListWord (C10SupplierRowInput.childList (decompositionOf sources)
    (Packets.live (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))
    (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)).occurrences)).length

/-- Call `j`'s row width, from the effective degree `deg j`. -/
def rowWidthOf (deg : Nat → Nat) (j : Nat) : Nat :=
  RowWidth.rw (Native.M2Of (deg j) (normalizedLiveCount q L)) (Native.U0Of q (normalizedLiveCount q L))
    (lenOf coordinate ph ci sources L target mode j)

end data

end
end NearCubicWires.SourceConstruction.TraceData
end
