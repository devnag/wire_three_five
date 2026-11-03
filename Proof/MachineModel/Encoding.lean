import Proof.MachineModel.OrdinaryUnaryTemplate
import Proof.Foundations.OrdinaryStreaming
import Proof.Amplification.RecoveryTimedExecution

/-! Ordered raw incidence data for the rows branch (outside supplier, partitioned
under `ExtIncidence`). A monomial stream over child indices and the row-major
incidence table it denotes: exactly the `rows.flatten` word read by the checked
polynomial bank. Pure list semantics; the machine lives in `ExtIncidence.Machine`.
Duplicate monomials stay separate rows; repeated indices inside one monomial
collapse; the empty monomial is an all-zero row; the empty stream is no row. -/
namespace NearCubicWires.ExtIncidence
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- One child index `d` as a shifted unary block (`d+1` marks, one terminator).
This is `RowIndexField.word (d+1)`, so existing index writers apply. -/
def block (d : ℕ) : List Bool := List.replicate (d+1) true ++ [false]
/-- One monomial: start mark, its index blocks in source order, end mark. -/
def monomialWord (m : List ℕ) : List Bool := true :: (m.flatMap block ++ [false])
/-- The ordered monomial stream, closed by one end-of-stream mark. -/
def stream (ms : List (List ℕ)) : List Bool := ms.flatMap monomialWord ++ [false]
/-- The incidence row of one monomial over `B` children. -/
def maskOf (B : ℕ) (m : List ℕ) : List Bool := List.ofFn (fun i : Fin B => decide (i.val ∈ m))

def blockCost (d : ℕ) : ℕ := 2*d+4
def monomialCost (B : ℕ) (m : List ℕ) : ℕ := 2*B+4+(m.map blockCost).sum
def cost (B : ℕ) (ms : List (List ℕ)) : ℕ := (ms.map (monomialCost B)).sum+1

@[simp] theorem block_length (d : ℕ) : (block d).length = d+2 := by simp [block]
theorem monomialWord_length (m : List ℕ) : (monomialWord m).length = (m.flatMap block).length+2 := by
  simp [monomialWord]
theorem stream_cons (m : List ℕ) (ms : List (List ℕ)) : stream (m :: ms) = monomialWord m ++ stream ms := by
  simp [stream]


/-! ## Local tape-cell lemmas -/


/-- The first `k` cells of a row, read in order. -/
def copied (L : List Bool) (k : ℕ) : List Bool := (List.range k).map (fun i => readTapeBit L i)

end NearCubicWires.ExtIncidence
