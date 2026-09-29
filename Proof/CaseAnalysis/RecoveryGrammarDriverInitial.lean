import Proof.CaseAnalysis.RecoveryGrammarCompiled
import Proof.CaseAnalysis.RecoveryGrammarDriverBank

/-! The two fresh paid backing tapes become the actual finite drivers,
then one physical step positions both heads for the original grammar scan. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
open LocalBitMultitape Composition RecoveryBoundedGrammarDriver
open RecoveryBoundedGrammarCold (scanHeads scanData)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def twoData (A : Fin 112→List Bool) (x y : List Bool):=data (data A x) y

theorem update_count (A : Fin 112→List Bool) (x y next : List Bool) :
    Function.update (twoData A x y) 113 next=twoData A x next := by
  funext i
  refine Fin.addCases (m:=113) (n:=1) (fun j=>?_) (fun j=>?_) i
  · have hj : (j.castAdd 1 : Fin 114)≠113 := by
      intro he;have hv:=congrArg Fin.val he;change j.val=113 at hv;omega
    simp only [Function.update_of_ne hj,twoData,data,Fin.addCases_left]
  · fin_cases j
    simp [twoData,data,Function.update,Fin.addCases]

def initialBudget (bound count : ℕ):=((2*bound+8)+1+(2*count+8))+1+1

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarDriverBank
