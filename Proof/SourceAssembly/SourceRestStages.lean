import Proof.SourceAssembly.SourceRequestResidentProducer
import Proof.SourceAssembly.SourceCyclePad
import Proof.SourceAssembly.SourcePrologue
import Proof.Circuits.MatrixBucketDimensionsIncrement
import Proof.Packets.PacketsMetaContract

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-! ## 2. The monomial cursor -/

/-- The cursor machine on its three local tapes `[curT, cur, scratch]`: increment the template, then read it out. -/
def cursorMachine :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (0 : Fin 3)) MatrixBucketDimensions.Increment.machine)
    (UWalkUnary.machine false false)

def cursorCost (m : Nat) : Nat := (2*m+5) + 1 + (2*(m+1)+6)

/-! ## 3. One metadata stage, docked and padded -/

end
end NearCubicWires.SourceConstruction.Rest
end
