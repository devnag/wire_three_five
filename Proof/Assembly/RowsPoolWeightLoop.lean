import Proof.Assembly.RowsPoolWeightBody

/-! The original arity driver traverses every native weight and every
physical live-mask coordinate once. The output has the same arity; live
weights are replaced by zero, never deleted. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Item:=ℤ×Bool
def word (xs : List Item):=xs.flatMap (fun x=>intWord x.1)
def mask (xs : List Item):=xs.map Prod.snd
def saved (xs : List Item) (backing : List Bool):=
  xs.foldl (fun bs x=>DecompositionSource.Fields.saved x.1 bs) backing
noncomputable def loop:=RepeatMachine.machine body (fun _ _=>true)

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
