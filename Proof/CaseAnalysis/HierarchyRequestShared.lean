import Proof.CaseAnalysis.HierarchyRequestInput

/-! Build the common hierarchy word directly from the already retained
refuter answer. Static input aliasing preserves the final address and all
other old data; the complete original request construction remains paid. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyRequest.Shared
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (k t : Nat) := t+CloseoutHierarchyRequest.tapes k
def old (k : Nat) {t : Nat} (i : Fin t) : Fin (tapes k t) := i.castAdd (CloseoutHierarchyRequest.tapes k)
def bank (k : Nat) {t : Nat} (source : Fin t) (j : Fin (CloseoutHierarchyRequest.tapes k)) :
    Fin (tapes k t) := if j.val=2 then old k source else j.natAdd t
def input (k : Nat) {t : Nat} (ambient : Fin t → List Bool) : Fin (tapes k t) → List Bool :=
  Fin.addCases ambient (fun _ => [])

theorem bank_injective (k : Nat) {t : Nat} (source : Fin t) : Function.Injective (bank k source) := by
  intro a b h
  have hv := congrArg Fin.val h
  have hs := source.isLt
  apply Fin.ext
  dsimp only [bank,old] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

theorem bank_other (k : Nat) {t : Nat} (source i : Fin t) (hi : i ≠ source)
    (j : Fin (CloseoutHierarchyRequest.tapes k)) : bank k source j ≠ old k i := by
  intro h
  have hv := congrArg Fin.val h
  have ht := i.isLt
  by_cases hj : j.val=2
  · simp only [bank,hj,if_true,old,Fin.val_castAdd] at hv
    exact hi (Fin.ext hv.symm)
  · simp only [bank,hj,if_false,old,Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

def machine (k C : Nat) {t : Nat} (source : Fin t) :=
  RecoveryFocus.machine (bank k source) (CloseoutHierarchyRequest.machine k C)

end
end NearCubicWires.RepairSource.CloseoutHierarchyRequest.Shared
