import Proof.SourceAssembly.SourceFactorSelRunBound
import Proof.SourceAssembly.SourcePoolIndexReady

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-! ## Sizes -/

/-- The local universe size. -/
def nW (w C k : Nat) : Nat := 754 + 2 * w + 2 * C + 2 * k
/-- W's region size in the host (everything from local `29` on). -/
def gwW (w C k : Nat) : Nat := 725 + 2 * w + 2 * C + 2 * k

def o4 (w : Nat) : Nat := 61 + w
def o5 (w C k : Nat) : Nat := 199 + w + C + k
def o6 (w C k : Nat) : Nat := 221 + 2 * w + C + k
def o7 (w C k : Nat) : Nat := 226 + 2 * w + C + k
def o8 (w C k : Nat) : Nat := 731 + 2 * w + 2 * C + 2 * k
def o9 (w C k : Nat) : Nat := 748 + 2 * w + 2 * C + 2 * k
def o10 (w C k : Nat) : Nat := 751 + 2 * w + 2 * C + 2 * k

/-- Unfold every size and close a linear goal. -/
macro "wz" : tactic => `(tactic| (simp only [nW, gwW, o4, o5, o6, o7, o8, o9, o10] at *; omega))

/-! ## The ten stage docks, by value -/


section vals


end vals

section maps


/-! Injectivity through a left inverse on the shared ports. -/

/-! Left inverses on the shared ports (`< 30`). -/



end maps

/-! ## The target words, the producing stage, the bank invariant -/


end
end NearCubicWires.SourceFactorSel.Words

