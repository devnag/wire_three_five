import Proof.SourceAssembly.SourceFactorSelNat

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.HdrBlock
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation
noncomputable section

/-- The printer's dock: its scratch `0..21` on `8..29`, its resident `22 ↦ 0` (`1^k`), driver `23 ↦ 5`, log `24 ↦ 6`. -/
def natSl (j : Fin 25) : Fin 35 :=
  if j.val = 22 then 0 else if j.val = 23 then 5 else if j.val = 24 then 6 else ⟨8 + j.val, by omega⟩

/-- The header stage's dock: the five fields `1..4, 28`, scratch `30..33, 34`, output `7`. -/
def hdSl : Fin 11 → Fin 35 := ![1, 2, 3, 4, 28, 30, 31, 32, 33, 7, 34]

/-- **The header block** (ONE fixed machine). -/
def hdrM := Composition.machine (RecoveryFocus.machine natSl Nat.natM) (Header.stage hdSl)

def hdrCost (mode : Bool) (q L target k D : Nat) : Nat :=
  Nat.natCost k D + 1 + SourceRequest.FieldPass.cost 5 (Header.fields mode q L target k)

end
end NearCubicWires.SourceFactorSel.HdrBlock

