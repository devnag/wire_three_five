import Proof.Hierarchy.CompetitorRationalNumerators

/-! One exact rational addition on the fixed global scalar width. Its actual
ordinary program pays for both cross-numerators, widening the denominator,
the denominator product, and restoring that product to the reusable width.
The small-width fit is a fold invariant, not a change to the source theorem. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRationalSum
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalProducts CompetitorRationalDecision CompetitorRationalNumerators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (j : Fin 67) : Fin 88 := j.castAdd 21
def wideSlots : Fin 5 → Fin 88 := ![6,4,67,68,69]
def multiplySlots (j : Fin 14) : Fin 88 :=
  if j.val=0 then 5 else if j.val=8 then 67 else if j.val=9 then 6
  else ⟨70+j.val,by omega⟩
def cropSlots : Fin 5 → Fin 88 := ![84,73,85,86,87]
noncomputable def numeratorProgram := RecoveryFocus.machine nativeSlots CompetitorRationalDecision.machine
noncomputable def wideProgram := RecoveryFocus.machine wideSlots ClockNormalize.machine
noncomputable def multiplyProgram := RecoveryFocus.machine multiplySlots HierarchyMultiplyEntry.machine
noncomputable def cropProgram := RecoveryFocus.machine cropSlots ClockNormalize.machine
noncomputable def machine := Composition.machine numeratorProgram
  (Composition.machine wideProgram (Composition.machine multiplyProgram cropProgram))

theorem resize_prefix (b w x : ℕ) (h : b≤w) :
    ClockNormalize.resize b (binary w x)=binary b x := by
  induction b generalizing w x with
  | zero => rfl
  | succ b ih =>
    cases w with
    | zero => omega
    | succ w => simp only [binary,ClockNormalize.resize]; rw [ih w (x/2) (by omega)]

end NearCubicWires.RepairOrdinary.CompetitorRationalSum
