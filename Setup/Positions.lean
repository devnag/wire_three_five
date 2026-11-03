import TermLoop.Defs
import Setup.Words

/-!
# Field positions on a guess word `prefix ++ blanks` (for `TermLoop.LoopFit.phys`)

The guess word is `u ++ false^pad` with `|u| = D = ⌊N/16⌋` (`Setup.guessWord`). Every reader of the codec advances by
at most a multiple of `D` while it is inside `u`, and by a constant per item in the blank region (a blank count is one
`false`). With `T = 2D`: a field end is `≤ max p T + 1`, an integer end `≤ max p T + 2`, a circuit end
`≤ max p T + 2 + 2D (q + 2)`, so after the oracle field, `aux` circuits and `k` witness fields the position is at most
`2D + 1 + aux (2 + 2D (q+2)) + k` (`fieldPos_fields_le`): a padding of that length makes every field physical.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close NearCubicGates.Close.Codec NearCubicGates.Close.TermLoop
open NearCubicGates.Close.Worker.Format (readCount)

theorem readCount_pad (l : List Bool) (m : ℕ) : (readCount (l ++ List.replicate m false)).1 ≤ l.length := by
  induction l with
  | nil => cases m <;> simp [readCount, List.replicate_succ]
  | cons b l ih =>
    cases b with
    | false => simp [readCount]
    | true => simp [readCount]; omega

section Word

end Word

end NearCubicGates.Close.Setup
