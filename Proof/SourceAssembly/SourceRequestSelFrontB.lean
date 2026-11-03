import Proof.SourceAssembly.SourceRequestSelFrontA
import Proof.SourceAssembly.SourceRequestCurMoment
import Proof.SourceAssembly.SourceRequestCurPenalty
import Proof.SourceAssembly.SourceRequestCurClause
import Proof.SourceAssembly.SourceFactorSelCountRead

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelFront
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## Docks -/

def crL (k : Fin 379) : Fin NF :=
  if k.val = 0 then 19 else if k.val = 188 then 200 else ⟨300 + k.val, by have := k.isLt; unfold NF; omega⟩
def crR (k : Fin 379) : Fin NF :=
  if k.val = 0 then 19 else if k.val = 188 then 201 else ⟨700 + k.val, by have := k.isLt; unfold NF; omega⟩



def fLp : Phase → Fin NF
  | .penalty => 185
  | .clause => 130
  | .moment => 250
def fRp : Phase → Fin NF
  | .penalty => 189
  | .clause => 142
  | .moment => 251


def ntSl (ph : Phase) (j : Fin 23) : Fin NF :=
  if j.val = 0 then 669 else if j.val = 1 then 1069 else if j.val = 2 then fLp ph else if j.val = 3 then fRp ph
  else if j.val = 4 then 33 else if j.val = 5 then 40 else ⟨1100 + j.val, by have := j.isLt; unfold NF; omega⟩

def curSl (ph : Phase) (j : Fin 128) : Fin NF :=
  if j.val = 0 then 20 else if j.val = 1 then 669 else if j.val = 2 then 1069 else if j.val = 3 then fLp ph
  else if j.val = 4 then fRp ph else if j.val = 5 then 41 else ⟨1200 + j.val, by have := j.isLt; unfold NF; omega⟩

/-- The phase's cursor. -/
def curMach : Phase → (Σ s, Machine 128 s)
  | .moment => ⟨_, CurMoment.momentM⟩
  | .penalty => ⟨_, CurPenalty.penaltyM⟩
  | .clause => ⟨_, CurClause.clauseM⟩

/-- **Front B.** -/
def frontB (ph : Phase) :=
  Composition.machine (RecoveryFocus.machine crL SourceFactorSel.CountRead.countM)
  (Composition.machine (RecoveryFocus.machine crR SourceFactorSel.CountRead.countM)
  (Composition.machine (RecoveryFocus.machine (ntSl ph) (SourceFactorSel.Count.machine ph).2)
    (RecoveryFocus.machine (curSl ph) (curMach ph).2)))




def costB (ph : Phase) (bits : List Bool) (iL iR : Nat) (sL sR nL nR : Bool) (JL JR : Nat) : Nat :=
  SourceFactorSel.CountRead.countCost bits iL + 1 + (SourceFactorSel.CountRead.countCost bits iR + 1 +
    (SourceFactorSel.Count.cost ph sL sR nL nR JL JR + 1 + curCost JL JR))

end
end NearCubicWires.SourceRequest.SelFront

