import Proof.CaseAnalysis.WitnessFamilyCapacity

/-! The already-retained N counter pays both family capacities without
rescanning the original input or disturbing the live source/policy bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity.Call
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (E : ℕ):=FamilyCapacity.tapes E
def old (E : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra E):=i.castAdd _
def slots (E : ℕ) {t : ℕ} (source : Fin t) (i : Fin (extra E)) : Fin (t+extra E):=
  if i.val=0 then old E source else i.natAdd t
def machine (E K : ℕ) {t : ℕ} (source : Fin t):=
  RecoveryFocus.machine (slots E source) (FamilyCapacity.machine E K)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity.Call
