import Proof.Supplier.EquationScalarStreamLayout
import Proof.Supplier.EquationZeroField

/-! Small forward source pass: widen all weights and branch on the actual
odd flag to emit the optional ignored coordinate. -/
namespace NearCubicWires.RepairOrdinary.EquationCut
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def weightSlots : Fin 3→Fin 5 := ![0,1,2]
def zeroSlots : Fin 2→Fin 5 := ![3,1]
def scalarSlots : Fin 2→Fin 5 := ![0,1]
def weightProgram := RecoveryFocus.machine weightSlots EquationWidenLoop.machine
def zeroProgram := RecoveryFocus.machine zeroSlots EquationZeroField.machine
def scalarProgram := RecoveryFocus.machine scalarSlots EquationWiden.machine
def weightSizes : Fin 2→Nat := ![Fintype.card (RepeatMachine.Control 5),4]
def weightPrograms : (j : Fin 2)→Machine 5 (weightSizes j) :=
  Fin.cases weightProgram (Fin.cases zeroProgram (fun i=>nomatch i))
def weightNext (j : Fin 2) (_ : Fin (weightSizes j)) (bs : Fin 5→Bool) : Option (Fin 2) :=
  if j=0 ∧ bs 4=true then some 1 else none
def weightMachine := RecoveryCalls.machine weightSizes weightPrograms 0 weightNext
def baseTail := Composition.machine scalarProgram scalarProgram
def base := Composition.machine weightMachine baseTail
def restored := CursorRestore.machine base 0



theorem calls_forward {t k : Nat} (sizes : Fin k→Nat)
    (programs : (j : Fin k)→Machine t (sizes j)) (first : Fin k)
    (next : (j : Fin k)→Fin (sizes j)→(Fin t→Bool)→Option (Fin k)) (i : Fin t)
    (hf : ∀ j,CursorRestore.NoLeft (programs j) i) :
    CursorRestore.NoLeft (RecoveryCalls.machine sizes programs first next) i := by
  intro q bs a ha
  cases hc : (RecoveryCalls.controlCode sizes).symm q with
  | none => simp [RecoveryCalls.machine,hc] at ha
  | some j =>
    simp only [RecoveryCalls.machine,hc] at ha
    split at ha
    · cases ha; simp
    · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      subst a
      exact hf j.1 j.2 bs b hb

end
end NearCubicWires.RepairOrdinary.EquationCut
