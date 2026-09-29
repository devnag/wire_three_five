import Proof.MachineModel.TopDownPaidReusable

/-! The actual full-state hrow application: source k is the retained complete
framed row stream at its kth consumed prefix, fixed templates and zero-backed
private storage. The only growing word is the raw count output. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer machine
  P1TopDownPaidReloadCore.rawMachine P1TopDownPaidReusableBody.machine

structure Datum where
  row : EquationRow.Input
  C : Nat
  Q : Nat
  f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Nat
  select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool

noncomputable def Datum.word (a : WilliamsAlgorithm) (d : Datum) := P1TopDownPaidReusable.word a d.row d.C d.Q d.select

structure Valid (a : WilliamsAlgorithm) (B R S : Nat) (d : Datum) : Prop where
  capacity : (Header.stream d.row).length≤d.C
  precision : d.Q≤(EquationRow.request d.row).p
  values : ∀ i j,d.f i j<2^d.Q
  meaning : ∀ i : Fin ((EquationRow.request d.row).U*(EquationRow.request d.row).U),
    Int.ModEq ((2 : Int)^d.Q)
      (SupplierPrinter.weightedDominance (leftScore (EquationRow.request d.row))
        (rightScore (EquationRow.request d.row)) (weight (EquationRow.request d.row)) i.divNat i.modNat)
      (d.f i.divNat i.modNat)
  rewind : P1TopDownPaidReloadCore.fuel a d.row d.C d.Q≤R
  buffer : RowPayload.budget (scalarWidth (EquationRow.request d.row) d.Q)≤B
  reset : B+1≤R
  workspace : P1TopDownPaidReloadCore.budget a d.row d.C d.Q B+1≤S
  bufferWorkspace : B≤S

noncomputable def source (a : WilliamsAlgorithm) (ds : List Datum) (S R B : Nat)
    (k : Nat) (out : List Bool) :=
  (⟨(machine a).start,heads a ((ds.take k).flatMap (Datum.word a)).length out,
    bank a (ds.flatMap (Datum.word a)) S R B out⟩ : Configuration _ _)

end NearCubicWires.P1TopDownPaidReusable
