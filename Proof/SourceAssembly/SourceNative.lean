import Proof.SourceAssembly.SourceRowWidth
import Proof.CaseAnalysis.FiveNativeResources
import Proof.Assembly.Values

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RepairSource RepairSource.CloseoutFinal SupplierEstimator SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace NearCubicWires.SourceConstruction.Native
noncomputable section

/-- The uniform constant `U0 = 3(K+1) + 2⌈(q−K)/2⌉ + 6`. -/
abbrev U0Of (q K : Nat) : Nat := 3 * (K + 1) + 2 * ((q - K + 1) / 2) + 6

abbrev M2Of (deg K : Nat) : Nat := 2 * (deg * (K + 1))

end
end NearCubicWires.SourceConstruction.Native
end
