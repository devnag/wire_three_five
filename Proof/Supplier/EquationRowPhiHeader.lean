import Proof.MachineModel.Runs
import Proof.Supplier.EquationHeader

/-! The Theorem 2.5 row producer writes the φ part of the matrix-request header for its identity
instance (weight count `d`, identity columns; paper3 alg:pullback P3:1623-1671 with φ = id). Two
stages extend the producer's 126-tape run without new tapes: an erase of one retained unary count
(bank 24) and `natWord d` appended by the existing header appender, whose sixteen work tapes are
all-false retained banks entered by zero padding. The identity columns follow in
`EquationRowPhiColumns`. -/
namespace NearCubicWires.RepairOrdinary.EquationRowPhiHeader
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ### Stage 1: erase bank 24 (`replicate (2d+1) true`) with driver bank 26 and recording bank 31. -/

def eraseSlots : Fin 3 → Fin 126 := ![54,56,61]
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)


/-! ### Stage 2: append `natWord d` with sixteen all-false work tapes. -/

/-- Local 0: the first header program's retained `replicate d true` (tape 62); locals 1..16: the
all-false banks 5,7,9,11,13,15,16,17,19,21,23,24(erased),25,27,29,31; local 17: the output. -/
def appendSlots : Fin 18 → Fin 126 := ![62,35,37,39,41,43,45,46,47,49,51,53,54,55,57,59,61,110]
noncomputable def append := RecoveryFocus.machine appendSlots EquationHeaderAppend.machine


/-! ### Stage 3: a five-tape column writer (count, output, three scratch tapes). -/

/-- Local 0: the appended count copy (tape 35); local 1: the output; locals 2..4: three blank
extras whose final all-false contents fit back inside their allocated capacity. -/
def writerSlots : Fin 5 → Fin 126 := ![35,110,111,112,113]

end NearCubicWires.RepairOrdinary.EquationRowPhiHeader
