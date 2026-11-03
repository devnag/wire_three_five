import Proof.MachineModel.OrdinaryMatrixScoreLeftCycle
import Proof.MachineModel.OrdinaryMatrixScorePhi

/-! The record-cycle layout with the row transform `φ` (paper3 `alg:pullback`, P3:1623-1671).

The existing 27-tape record carrier (`MatrixScoreLeftCycle.tapes`) is kept unchanged and one
tape is appended: tape 27 holds the columns of `φ`, `columnsWord d cols`, where `d` is the
weight count (the carrier's sentinel width) and `cols` the `φ`-columns, one per row bit. The
record body never reads tape 27; only the advance between records does.

`AdvanceSpec` is the step contract for the replaced `MatrixScoreAdvance`: bump the stable id
and overwrite the assignment with `φ(id+1) = MatrixScorePhi.value cols (id+1)`. Its type names
the paper's quantity: the assignment after the step IS the center-bit vector of the next id. -/
namespace NearCubicWires.RepairOrdinary.MatrixScorePhiLayout
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

/-- Heads of the 28-tape carrier: the cycle's heads, and the `φ` tape at cell 0. -/
def heads (opos : ℕ) : Fin 28 → ℕ :=
  Fin.addCases (m := 27) (n := 1) (motive := fun _ => ℕ) (MatrixScoreLeftCycle.heads opos) (fun _ => 0)

/-- Tapes of the 28-tape carrier: the cycle's tapes, and the `φ` columns as tape 27. -/
def tapes (source assignment : List Bool) (d c cap w x m id template : ℕ)
    (work : Fin 12 → List Bool) (driver counter out : List Bool) (returnCap : ℕ) (cols : List ℕ) :
    Fin 28 → List Bool :=
  Fin.addCases (m := 27) (n := 1) (motive := fun _ => List Bool)
    (MatrixScoreLeftCycle.tapes source assignment d c cap w x m id template work driver counter out returnCap)
    (fun _ => MatrixScorePhi.columnsWord d cols)

/-- The fixed budget of the new advance: the id increment of today's `MatrixScoreAdvance`
(`4m+2`), one composition step, and one `φ` evaluation. -/
def advanceBudget (d k m c : ℕ) : ℕ := (4*m+2)+1+MatrixScorePhi.budget k d m c

end NearCubicWires.RepairOrdinary.MatrixScorePhiLayout
