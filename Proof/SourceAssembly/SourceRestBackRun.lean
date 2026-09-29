import Mathlib
import Proof.Packets.PacketsLayout
import Proof.SourceAssembly.SourceCyclePad
import Proof.SourceAssembly.SourceRequestFactorLoop
import Proof.SourceAssembly.SourceRestLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- Close a value (in)equality: `simp`, then `omega` if anything is left. -/
macro "vsimp" : tactic => `(tactic| (first | (simp; done) | (simp; omega) | omega))

section

end

end
end NearCubicWires.SourceConstruction.Rest
end
