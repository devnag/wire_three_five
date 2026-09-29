import Proof.CaseAnalysis.WitnessSumDock

/-! A successful sum clears its one private header/count bank with the
already paid H driver. The source arity, term cap, verdict and native
count stream survive. No failed branch enters this reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumReset
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateSlot (i : Fin 524) : Fin 528 :=
  ⟨if i.val<499 then i.val else if i.val=499 then 500 else if i.val<523 then i.val+3 else 527,
    by split_ifs <;> omega⟩
def scratch (i : Fin 524) := SumDock.slots (privateSlot i)
def slots : Fin 526 → Fin 3061 :=
  Fin.addCases (m:=524) (n:=2) (motive:=fun _=>Fin 3061) scratch ![2530,2531]
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 524)

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumReset
