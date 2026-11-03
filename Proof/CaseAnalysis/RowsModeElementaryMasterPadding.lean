import Proof.CaseAnalysis.RowsModeElementaryReusable

/-! Fixed zero padding on the retained numeric masters permits physical
counter overwrites between degree calls. The growing output is unpadded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsModeElementaryLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def masterCaps (C : Nat) (i : Fin 52) : Nat := if 46 ≤ i.val ∧ i.val < 50 then C else 0
noncomputable def paddedBlank (w k M C : Nat) (out : List Bool) : Fin 52→List Bool:=
  fun i=>ZeroPadding.pad (masterCaps C i) (blank w k M C out i)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReusable
