import Proof.CaseAnalysis.RowsDegreeCoefficient
import Proof.CaseAnalysis.RowsEnumeratedCuts

/-! A complete fixed-degree row call starts with a blank coefficient cache.
Unary j and p produce (-2)^j once, then the actual positional enumeration
and signed-cut writer run at their retained native cache and output cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsComputedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficientSlots (i : Fin 14) : Fin 103 :=
  if i.val=12 then 48 else i.natAdd 89

noncomputable def first := RecoveryFocus.machine coefficientSlots CloseoutRowsDegreeCoefficient.machine
noncomputable def last := TapeEmbedding.machine 14 CloseoutRowsEnumeratedCuts.machine
noncomputable def machine := Composition.machine first last
noncomputable def body {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsEnumeratedCuts.input state gs p F w (j+1) rows out ((-2 : ℤ)^j)
noncomputable def input {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n))
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Configuration 103 s :=
  ⟨state,Fin.addCases (m := 89) (n := 14) (motive := fun _ => ℕ)
      (body state gs p F w j rows out).heads (fun _ => 0),
    Fin.addCases (m := 89) (n := 14) (motive := fun _ => List Bool)
      (Function.update (body state gs p F w j rows out).tapes 48 [])
      (CloseoutRowsDegreeCoefficient.input j p)⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsComputedCuts
