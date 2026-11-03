import Proof.SourceAssembly.SourceFactorSelModes

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.DescF
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierPipeline SourceInterfaces
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest
open Desc (Kind gdesc cp sysW sysCost dT copy_step pad_nil read_true read_blank stop_step sys_run flagS flagO)
open Modes (kindOf bmOf bitsOf thr_descAt sym_descAt tape_length)
noncomputable section

/-! ## The machine -/

/-- The original writer, framed input: `RepairOrdinary.frame bits` (port 3) → 4, 9; template → 5, 10; `1^P` → 6, 11;
`1^W` → 7, 12; `1^L` → 8, 13; flag O → 15. -/
def origWF := Composition.machine (cp 3 15) (Composition.machine (cp 4 16) (Composition.machine (cp 5 17)
  (Composition.machine (cp 6 18) (Composition.machine (cp 7 19) (Composition.machine (cp 3 20)
  (Composition.machine (cp 4 21) (Composition.machine (cp 5 22) (Composition.machine (cp 6 23)
  (Composition.machine (cp 7 24) (cp 1 26))))))))))

/-- **The descriptor writer (framed code)**: flag S → systematic writer; else flag O → original writer; else stop. -/
def machine := CloseoutRowsOriginalSwitch.machine sysW
  (CloseoutRowsOriginalSwitch.machine origWF (CloseoutRowsOriginalSwitch.stop 27) (1 : Fin 27)) (0 : Fin 27)

def origCostF (D : Nat) : Nat := 11 * (2 * D + 4) + 10

def costF : Kind → Nat → Nat
  | .absent, _ => 0 + 2 + 2
  | .sys, D => sysCost D + 2
  | .orig, D => origCostF D + 2 + 2

/-! ## Per mode -/

section

end


end
end NearCubicWires.SourceFactorSel.DescF
