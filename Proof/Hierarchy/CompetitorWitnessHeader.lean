import Proof.Hierarchy.CompetitorWitnessHeaderFlags
import Proof.Amplification.RecoveryFocusDock

/-! Complete all-input canonical witness-header guard. One fixed ordinary
machine starts with exactly the input/witness frames and blank workspace,
extracts the header, classifies every control field, and leaves a validity
bit while preserving both nested payloads. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev kindStates := Fintype.card (RecoveryCalls.Control CompetitorWitnessKind.sizes)
def sizes : Fin 6 → ℕ := ![kindStates,kindStates,kindStates,kindStates,kindStates,2]
noncomputable def programs : (j : Fin 6) → Machine 148 (sizes j)
  | ⟨0,_⟩=>program 0
  | ⟨1,_⟩=>program 1
  | ⟨2,_⟩=>program 2
  | ⟨3,_⟩=>program 3
  | ⟨4,_⟩=>program 4
  | ⟨5,_⟩=>last
  | ⟨n+6,h⟩=>False.elim (by omega)
def next (j : Fin 6) (_ : Fin (sizes j)) (_ : Fin 148 → Bool) : Option (Fin 6) := ![some 1,some 2,some 3,some 4,some 5,none] j
noncomputable def guard := RecoveryCalls.machine sizes programs 0 next

noncomputable def first := TapeEmbedding.machine 26 CompetitorWitnessTriple.machine
noncomputable def machine := Composition.machine first guard
def input (x bits : List Bool) : Fin 148 → List Bool := Fin.addCases
  (m := 122) (n := 26) (motive := fun _=>List Bool) (CompetitorWitnessTriple.input x bits) (fun _=>[])

theorem input_eq (x bits : List Bool) (i : Fin 148) : input x bits i=
    if i.val=0 then frame x else if i.val=1 then frame bits else [] := by
  refine Fin.addCases (m := 122) (n := 26) ?_ ?_ i
  · intro j
    rw [input,Fin.addCases_left,CompetitorWitnessTriple.input]
    rfl
  · intro j
    rw [input,Fin.addCases_right]
    have h0 : (j.natAdd 122).val≠0 := by simp only [Fin.val_natAdd];omega
    have h1 : (j.natAdd 122).val≠1 := by simp only [Fin.val_natAdd];omega
    rw [if_neg h0,if_neg h1]

end NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
