import Proof.CaseAnalysis.WitnessSourceCounts
import Proof.CaseAnalysis.WitnessCorePolicy

/-! One source metadata pass and one coefficient policy. The original
PCPP output and the public cache domain at head one are used directly;
the exact V, actual clause bits, q0 and coefficient bit cap are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (D : ℕ):=CorePolicy.tapes D+43
def countSlots (D : ℕ) (i : Fin 42) : Fin (tapes D):=⟨i.val,by dsimp only [tapes];omega⟩
def coreSlot (D : ℕ) : Fin (tapes D):=⟨42,by dsimp [tapes,CorePolicy.tapes];omega⟩
def policySlots (D : ℕ) (i : Fin (CorePolicy.tapes D)) : Fin (tapes D):=
  ⟨if i.val=0 then 42 else if i.val=5 then 38 else 43+i.val,by
    dsimp only [tapes];split_ifs <;> omega⟩
def q0Slot (D : ℕ):=policySlots D (CorePolicy.q0Slot D)
def capSlot (D : ℕ):=policySlots D (CorePolicy.capSlot D)
def count (D : ℕ):=RecoveryFocus.machine (countSlots D) SourceCounts.machine
def policy (D copies : ℕ) (delta : ℚ):=
  RecoveryFocus.machine (policySlots D) (CorePolicy.machine D copies delta)
def machine (D copies : ℕ) (delta : ℚ):=Composition.machine (count D) (policy D copies delta)
def budget (D copies core a b cb : ℕ) (delta : ℚ):=
  SourceCounts.budget a b cb+1+CorePolicy.budget D copies core cb delta


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
