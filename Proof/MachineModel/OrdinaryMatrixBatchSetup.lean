import Proof.MachineModel.OrdinaryMatrixScoreRawRanksBounds

/-! The actual all-gates request, before any matrix exists, supplies d, p,
U and the gate count with their physical native and unary drivers. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchSetup
open LocalBitMultitape SignedSortKey MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 11 → Fin 90 := ![1,80,81,82,83,84,85,86,87,88,89]
noncomputable def first := TapeEmbedding.machine 10 MatrixScoreSetup.machine
noncomputable def last := RecoveryFocus.machine slots MatrixDimensionPrepare.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 90 → List Bool := fun i => if i=0 then physicalInput r else []
/-- The word after the gate count: the weight count, the columns of `φ` (the rest of `header r`), then
the cuts. This setup parses only `d`, `p` and the gate count; `MatrixBatchWidthSetup` parses the rest of the
header later, from the head position `gatesEnd r`. -/
def tail (r : Request) : List Bool :=
  natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++r.cuts.flatMap (cutWord r.p)
/-- Where the gate count ends on the copied word: `|natWord d ++ natWord p ++ natWord Gates|`. -/
def gatesEnd (r : Request) : ℕ := (natWord r.d++natWord r.p++natWord r.Gates).length
theorem word_eq (r : Request) : natWord r.d++natWord r.p++(natWord r.Gates++tail r)=word r := by
  simp only [word,header,tail,List.append_assoc]
def budget (r : Request) := MatrixScoreSetup.budget r.d r.p (natWord r.Gates++tail r)+1+
  MatrixDimensionPrepare.budget (natBitLength r.Gates) r.Gates

end NearCubicWires.RepairOrdinary.MatrixBatchSetup
