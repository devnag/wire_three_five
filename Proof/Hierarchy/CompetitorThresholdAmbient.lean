import Proof.Hierarchy.CompetitorThresholdConstants

/-! The literal fixed-threshold producer beside the retained scalar fold.
Its fresh work tapes begin blank; the global scalar cursor and loop driver
are preserved while the two physical width words are reused. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 94) : Fin 110 := i.castAdd 16
def constantSlots (i : Fin 17) : Fin 110 :=
  if i.val=0 then 6 else if i.val=1 then 84 else ⟨i.val+93,by omega⟩
noncomputable def constantsProgram (k : ℕ) (q : ℚ) :=
  RecoveryFocus.machine constantSlots
    (CompetitorThresholdConstants.machine k (CompetitorThresholdDecision.numerator q) q.den)


noncomputable def clearProgram := RecoveryFocus.machine native (CompetitorSumFold.clearProgram workSlot)


end NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
