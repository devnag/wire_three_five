import Proof.Rows.FinalWalkStep
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.MachineModel.Runs
import Proof.Foundations.SupplierPrime

namespace NearCubicWires.RepairOrdinary.FinalPrimeRow
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Finite control

State `0` reads the flag cell and the target bit, state `1` halts.  States
`2..9` scan a frame marker and `10..17` scan a bit; in both groups the code
carries the latched selector, the delayed residue bit and the running carry. -/



/-! ## 2. The four local transitions -/

/-! ## 3. One sweep -/

/-! ## 4. The whole pass, including the entry read -/

/-! ## 5. Exact arithmetic of one sweep -/

/-! ## 6. The driven loop: the whole residue of one target modulo one prime -/

def cost (width : ℕ) : ℕ := 2 * (2 * width + 2) + 2


/-! ## 7. One prime row: the residue of a canonical target modulo one prime

`primesUpTo`'s members are the row index of Appendix A.13.  For such a prime,
`primeWidth` is the `modulusDigitCount`-plus-one word width the sweep needs,
`targetBits` is the MSB-first digit stream of the canonical target, and the
driven loop below reads the residue off in `K * (4 * primeWidth + 9) + 3`
ordinary steps. -/

end NearCubicWires.RepairOrdinary.FinalPrimeRow
