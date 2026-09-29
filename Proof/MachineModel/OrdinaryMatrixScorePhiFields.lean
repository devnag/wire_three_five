import Proof.MachineModel.OrdinaryMatrixScoreLeftLoop

/-! PIECE C / PIECE D interface: the per-gate native fields with the row transform `φ`.

Today the batch hands each gate call `MatrixScoreReusableRanks.fields r gate`, 41 tapes. With
`φ` (paper3 `alg:pullback`, P3:1623-1671) the weight count is `r.width` and the assignment is
`φ(n)`. The score traversal carries the `φ` columns on its carrier's tape 27, so the per-gate
layout gains slot 27 and the old slots `27..40` move to `28..41`:
* slot 1 (the initial assignment, `φ(0) = 0`) and slot 29 (the retained zero assignment, the
  old 28): `frame (binary r.width 0)`;
* slot 17, the weight-count sentinel: `UnaryTemplate.tape r.width`;
* NEW slot 27: the columns of `φ`, `MatrixScorePhi.columnsWord r.width r.cols`.
Piece D (the batch) must present exactly `fields r gate` before each gate call; piece C
(`ReusableRanks`, `RetainedRanks` and the score traversal below them) consumes it. -/
namespace NearCubicWires.RepairOrdinary.MatrixScorePhiFields
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreWeight (zeros)
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

/-- The 42 per-gate native fields with `φ`. -/
def fields (r : Request) (gate : Fin r.Gates) : Fin 42 → List Bool :=
  ![cutWord r.p (r.cuts.get gate),frame (binary r.width 0),[],[],[],[],List.replicate (r.S+1) true,
    [],[],[],[],[],[],[],[],List.replicate (C r) true,zeros (C r+1),UnaryTemplate.tape r.width,
    frame (binary (r.S+1) (2^r.S)),frame (binary (r.S+1) 0),[],[],frame (binary r.M 0),
    frame (binary r.M r.U),[],zeros (C r),[],MatrixScorePhi.columnsWord r.width r.cols,
    UnaryTemplate.tape r.U,frame (binary r.width 0),
    [],[],[],[],[],[],[],[],[],[],[],[]]

/-- Old slot `i` of today's 41-slot layout sits at `i` below 27 and at `i+1` from 27 on. -/
def oldSlot (i : Fin 41) : Fin 42 := if i.val<27 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩

end NearCubicWires.RepairOrdinary.MatrixScorePhiFields
