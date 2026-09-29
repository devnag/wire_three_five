import Proof.Wire_3_5.Primitive.Writers.CellUnit

/-! # PA (d), the writers' loop (base `Cells.ofScrub` over the unit machine)

The writer's loop runs the unit machine (`CellUnit.unitM`, embedded next to `e` workspace tapes) once per unit index
`j < bound`, scrubbing every tape but the request, the output and the counter between units (base
`Cells.ofScrub`: the scrub's capacity `R` above the unit's cost; `L = R + 2`). A unit starts at its blank cell state
(`CellState.blankCell`), padded to the scrub's cleared state (base `Scrub.cleared_entry`: empty streams, the register
tapes `regTape cap 0 = 0^(cap+1)` and the cell `[false]` are cleared tapes of length at most `R`).

* `loopH`, `loopA`: the loop's banks before unit `j`; `blank_H`, `blank_scratch`;
* **`loop_stage`**: from the decode spec at `j`, one unit as a loop stage (kept ports and the output head advanced);
* **`loopCells`**, **`loop_step`**: the whole loop as one `Step` (base `Cells.loopStep`), the output `flatMap emit`.

Paper quantity of the main type: the writer's output `(List.range bound).flatMap emit ++ [false]` (for the SYM writer
`SymFlat.symTape_flat`: C4's `BAT` word of the call). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CellLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank

section Loop
variable (cap : ℕ)

/-- The cell layout's tape count. -/
abbrev TT (x : ℕ) : ℕ := LNS x + 2 + LNR

/-- The kept tapes of a cell: the request, the output, the counter. -/
def kept (x : ℕ) (i : Fin (TT x)) : Bool :=
  decide (i = sTape (sk x 0)) || decide (i = sTape (sk x 1)) || decide (i = sTape (sk x 2))

theorem blank_H (x : ℕ) (w out : List Bool) (j : ℕ) :
    (wenc cap (blankCell x w out j)).H = fun i => if i = sTape (sk x 1) then out.length else 0 := by
  funext i
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s]
    by_cases hs : s = sk x 1
    · subst hs
      rw [if_pos rfl]
      simp [blankCell]
    · rw [if_neg (fun h => hs (sTape_inj h))]
      simp [blankCell, hs]
  · rw [wenc_H_c, if_neg (fun h => sTape_ne_c _ h.symm)]
  · rw [wenc_H_r, if_neg (fun h => sTape_ne_r _ _ h.symm)]
    rfl

theorem blank_scratch (x : ℕ) (w out : List Bool) (j : ℕ) (i : Fin (TT x)) (hi : kept x i = false) :
    ∃ k, k ≤ cap + 1 ∧ (wenc cap (blankCell x w out j)).A i = List.replicate k false := by
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · have h0 : s ≠ sk x 0 := fun h => by subst h; simp [kept] at hi
    have h1 : s ≠ sk x 1 := fun h => by subst h; simp [kept] at hi
    have h2 : s ≠ sk x 2 := fun h => by subst h; simp [kept] at hi
    refine ⟨0, by omega, ?_⟩
    rw [wenc_A_s]
    simp [blankCell, h0, h1, h2]
  · exact ⟨1, by omega, by rw [wenc_A_c]; rfl⟩
  · refine ⟨cap + 1, le_rfl, ?_⟩
    rw [wenc_A_r]
    exact regTape_zero cap

end Loop

end NearCubicWires.WireExponent3_5.PrimAsm.CellLoop
