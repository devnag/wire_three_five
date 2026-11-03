import Proof.Packets.SelBackSym

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelBackSym
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

section run
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- The four slots' cost at cursor record `σ` (SYM). -/
def fourCostS (bits : List Bool) (iL iR : Nat) (σ : Option Sel) (cwid cw D : Nat) : Nat :=
  SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 0) then iR else iL) (fIdx (facAt σ 0)) cwid cw D + 1 +
  (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 1) then iR else iL) (fIdx (facAt σ 1)) cwid cw D + 1 +
  (SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 2) then iR else iL) (fIdx (facAt σ 2)) cwid cw D + 1 +
  SourceFactorSel.Slot.slotCost bits (if fSide (facAt σ 3) then iR else iL) (fIdx (facAt σ 3)) cwid cw D))

/-- The back's cost (SYM): four slots ; header ; coefficient words. `Rc`-free. -/
def backSymCost {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (bits : List Bool) (iL iR : Nat)
    (σ : Option Sel) (cwid cw D q L target k K b : Nat) : Nat :=
  fourCostS bits iL iR σ cwid cw D + 1 + (SourceFactorSel.HdrBlock.hdrCost true q L target k D + 1 +
    SourceFactorSel.CoefR.coefRCost cw rhoW K b (rhoOf σ) (fun i => fTerm (facAt σ i.val))
      (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val)))

end run
end
end NearCubicWires.SourceRequest.SelBackSym

