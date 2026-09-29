import Proof.CaseAnalysis.WitnessSourcePolicy

/-! Alias the public source and head-one cache domain into the one-time
policy. Every old tape and cursor is retained, including the reusable cache. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (D : ℕ):=SourcePolicy.tapes D
def old (D : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra D):=i.castAdd (extra D)
def slots (D : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (i : Fin (extra D)) : Fin (t+extra D):=
  if i.val=0 then old D (fields 0) else if i.val=42 then old D (fields 1) else i.natAdd t
def machine (D copies : ℕ) (delta : ℚ) {t : ℕ} (fields : Fin 2→Fin t):=
  RecoveryFocus.machine (slots D fields) (SourcePolicy.machine D copies delta)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.Call
