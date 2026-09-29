import Proof.CaseAnalysis.WitnessOracleCap

/-! The exact cap checker aliases the two actual metadata counters. Every
old tape and head is retained, so the original native continuation reuses them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap.Call
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (G : ℕ):=Core.tapes (degree G)
def old (G : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra G):=i.castAdd (extra G)
def slots (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t) (i : Fin (extra G)) : Fin (t+extra G):=
  if i.val=0 then old G (fields 0) else if i.val=1 then old G (fields 1) else i.natAdd t

def machine (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t):=
  RecoveryFocus.machine (slots G fields) (OracleCap.machine G)
def flagSlot (G : ℕ) {t : ℕ} (fields : Fin 2→Fin t):=
  slots G fields (Core.flagSlot (degree G))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCap.Call
