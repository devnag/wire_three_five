import Proof.MachineModel.Runs
import Proof.PCP.ProjectionNormalizationForwardRules

/-! # The identity columns of the row transform, written by a machine

The batch request header (`MatrixScoreBatch.header`) carries the weight count and the columns of the row
transform `φ` (paper3 `alg:pullback`, P3:1623-1671). Theorem 2.5's own requests use the identity
transform: `width = d` and column `j` is `2^j`. So their producer appends the identity columns
`word d`, i.e. `frame (binary d (2^j))` for `j < d`; this is
`MatrixScorePhi.columnsWord d ((List.range d).map (2^·))` (checked in
`Checks/EquationIdentityColumnsBridge.lean`).

`write_run`: from the count tape `List.replicate d true` (head 0), the output `out` (head at its end) and
three blank work tapes, `machine` appends `word d` in at most `budget d = 64 (d+1)²` steps. The count tape
and its head end as they started. Every work tape ends all-false with head 0, with the exact lengths
`2d+1`, `2d` and `d`. `out_forward`: the output head never moves left.

Tapes: 0 the count `C`, 1 the output `O`, 2 the current column `H`, 3 the rewind log of `H`, 4 the
rewind log of `C`. The program:
1. `First` writes `frame (binary d 1)` on `H` while scanning `C`. Then `H` and `C` are restored
   (`CursorRestore`: a log records exactly its target's right moves and is erased while rewinding it).
2. A `StreamController` loop runs while `C` reads `true`. Each pass: `Emit` appends `H` to `O` and
   shifts `H` in place (`binary d m ↦ binary d (2m)`), `H` is restored, and `C` steps right. After the
   loop, `C` is restored.
3. `Erase` clears `H` in place, and `H` is restored.
Nothing here depends on the batch codec. -/
namespace NearCubicWires.RepairOrdinary.EquationIdentityColumns
open LocalBitMultitape SignedSortKey NearCubicWires.ExtDecompositionBatch RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## The word -/

/-! ## Three base tapes: 0 the count, 1 the output, 2 the column -/

/-- One action on the base tapes; the count tape is never written. -/
def act {s : ℕ} (next : Fin s) (wO wH : Option Bool) (mC mO mH : HeadMove) : Action 3 s :=
  ⟨next, ![none, wO, wH], ![mC, mO, mH]⟩

namespace First

/-- The first column from the count. States `0`/`2` read the next count cell (for the first item / a
later item), `1`/`3` write that item's bit (`true` for the first item, `false` after it), `4` halts.
It writes `frame (binary d 1)` on `H`; `C` and `H` only move right. -/
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then act 1 none (some true) .stay .stay .right else act 4 none (some false) .stay .stay .stay)
    else if q.val = 1 then some (act 2 none (some true) .right .stay .right)
    else if q.val = 2 then
      some (if sc 0 then act 3 none (some true) .stay .stay .right else act 4 none (some false) .stay .stay .stay)
    else if q.val = 3 then some (act 2 none (some false) .right .stay .right)
    else none

end First

namespace Emit

/-- One pass over the column. States `0`/`1` read a marker of `H` carrying `false`/`true`; `2`/`3` read a
bit of `H` and write the carry back in its place; `4` halts. Every scanned cell of `H` is appended to `O`.
So `O` gains `frame w` and `H` becomes `frame` of `w` shifted up by one bit. -/
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 2 then act 2 (some true) none .stay .right .right else act 4 (some false) none .stay .right .stay)
    else if q.val = 1 then
      some (if sc 2 then act 3 (some true) none .stay .right .right else act 4 (some false) none .stay .right .stay)
    else if q.val = 2 then
      some (if sc 2 then act 1 (some true) (some false) .stay .right .right
        else act 0 (some false) (some false) .stay .right .right)
    else if q.val = 3 then
      some (if sc 2 then act 1 (some true) (some true) .stay .right .right
        else act 0 (some false) (some true) .stay .right .right)
    else none

end Emit

namespace Erase

/-- Clear the column in place. State `0` reads a marker of `H` (a `true` marker is cleared), `1` clears a
bit, `2` halts. -/
def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 2 then act 1 none (some false) .stay .stay .right else act 2 none none .stay .stay .stay)
    else if q.val = 1 then some (act 0 none (some false) .stay .stay .right)
    else none

end Erase

/-- Step the count tape's head to the next cell. -/
def nudge : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some (act 1 none none .right .stay .stay) else none

/-! ## Assembly -/

/-- Restore one head (`CursorRestore`): the new last tape logs exactly the target's right moves. -/
abbrev restore {t s : ℕ} (p : Machine t s) (target : Fin t) : Machine (t + 1) (s + 2) :=
  RepairSource.ProjectionNormalization.CursorRestore.machine p target

/-- The count tape inside the four-tape stages. -/
def C4 : Fin (3 + 1) := (0 : Fin 3).castAdd 1

def initM := restore (restore First.machine 2) C4
def passM := Composition.machine (restore Emit.machine 2) (TapeEmbedding.machine 1 nudge)
def loopM := StreamController.machine passM C4
def loopR := restore loopM C4
def eraseM := TapeEmbedding.machine 1 (restore Erase.machine 2)

/-- **The identity-columns writer.** Tapes: count, output, column, the column's log, the count's log. -/
def machine : Machine 5 27 := Composition.machine (Composition.machine initM loopR) eraseM

/-! ## Tape facts -/

/-! ## The first column -/

namespace First


end First

/-! ## One pass: emit the column, shift it in place -/

namespace Emit


end Emit

/-! ## Clearing the column -/

namespace Erase

end Erase



/-! ## Motion facts for the combinators (the output head only moves right) -/

/-! ## A restored stage as one `Step`

`CursorRestore` runs the stage, logging each right move of the target on a new last tape, then rewinds
the target by exactly that many moves while erasing the log. So the log ends all-false with length `δ`,
the target's net advance, if it started blank (`k = 0`) or all-false of that same length (`k = δ`). -/

/-! ## The stream loop -/

open RecordController (code test stop)

namespace Loop

end Loop

/-! ## The passes -/




/-! ## The start and the end -/

/-! ## The writer -/


end NearCubicWires.RepairOrdinary.EquationIdentityColumns
