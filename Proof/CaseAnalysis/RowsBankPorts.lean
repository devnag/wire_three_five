import Proof.CaseAnalysis.RowsBankClear
import Proof.CaseAnalysis.RowsPacketLoad

/-! The exact fixed packet port set is the whole native bank except its
growing output and the two shared erase resources. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPorts
open LocalBitMultitape CloseoutRowsBankClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem written_apply {t : ℕ} (fields : Fin t→List Bool) (C : ℕ)
    (js : List (Fin t)) (data : Fin t→List Bool) (i : Fin t) :
    CloseoutRowsPacketLoad.written fields C js data i=
      if i∈js then ZeroPadding.pad C (fields i) else data i := by
  induction js generalizing data with
  | nil => rfl
  | cons j js ih =>
    rw [CloseoutRowsPacketLoad.written,ih]
    by_cases hm : i∈js
    · simp [hm]
    · by_cases he : i=j
      · subst i
        simp [hm]
      · simp [hm,he]

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPorts
