import Proof.MachineModel.NativeFamily

/-! The actual raw family has the literal row type consumed by the estimator.
The occurrence list and shared digit width are unchanged. -/
namespace NearCubicWires.ExtIncidence.NativeRowInput
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank {N : ℕ} (ps : List (List (List (Fin N)))):=ps.map rawRows

theorem bank_width {N : ℕ} (ps : List (List (List (Fin N)))) (w : ℕ)
    (hw : ∀ ms∈ps,ms.length<2^w) : ∀ rows∈bank ps,rows.length≤2^w:=by
  intro rows hr
  obtain ⟨ms,hm,rfl⟩:=List.mem_map.mp hr
  simpa only [rawRows,List.length_map] using (hw ms hm).le

def input (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (ps : List (List (List (Fin gs.length)))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (CloseoutRowsCacheInput.family gs (bank ps))).length^100≤2^s)
    (hw : ∀ ms∈ps,ms.length<2^w) : EquationRow.Input:=
  CloseoutRowsSharedInput.input s Q w gs (bank ps) hs hg (bank_width ps w hw)

end NearCubicWires.ExtIncidence.NativeRowInput
