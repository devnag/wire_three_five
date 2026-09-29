import Proof.Wire_3_5.Primitive.Writers.ShellXBoot

/-! # PA (d), the writer shell dimensioned by `n'` (ShellX), part 2: the whole writer run (`WriterRun`)

P3:3068-3084 (lem:primitive) and the writers' interface (`WriterIfaceJ`): from `frame req.word` the
SYM writer halts with its tape on the output port. This is `ShellD.shell_runD` with the scrub and the loop
dimensioned by `n' = 2^(2·kh + L)` (`ShellXBoot.bootX_step`), so the loop bound `b = CL(n'+1)^DL` and the scrub
capacity `R = C(n'+1)^D` reach the `2^(2·kh)·poly(n)` units of a call's tape:

`shellMX = MaskedReset (bootXM ; embed (ShellD.entryED) ; embed (ShellD.loopED))`

* **`shell_runX`**: `WriterIfaceJ.WriterRun (shellMX …) Bud (shellInX …) (shellOutX …) w
  ((List.range b).flatMap emit ++ [false])` for any unit machine whose decode (after the copy-in of the call's counts)
  meets `CellUnit.DecOK` at every unit `j < b`; `shellStageX` (a `WriterStage`).

Paper quantity of the main type: the writer's output tape `(List.range b).flatMap emit ++ [false]` (for the SYM writer
`SymFlat.symTape_flat`: C4's `BAT` word of the call). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline

section Run
variable {x D D2 Dv DL : ℕ}

/-- The scrub entry, on the real layout. -/
noncomputable def entryEX (x D D2 Dv DL C : ℕ) := TapeEmbedding.machine (EX x D D2 Dv DL) (entryED x D 0 D2 C)

/-- The unit loop with the data tape, on the real layout. -/
noncomputable def loopEX (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D D2 Dv DL : ℕ) :=
  TapeEmbedding.machine (EX W.x D D2 Dv DL) (loopED W decW D 0 D2)

/-- The shell's request port. -/
def shellInX (x D D2 Dv DL : ℕ) : Fin (STx x D D2 Dv DL + 1) := Fin.castAdd 1 (T0 x D D2 Dv DL)

/-- The shell's output port. -/
def shellOutX (x D D2 Dv DL : ℕ) : Fin (STx x D D2 Dv DL + 1) :=
  Fin.castAdd 1 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1))

theorem shellInX_ne_out : shellInX x D D2 Dv DL ≠ shellOutX x D D2 Dv DL := by
  intro h
  have := congrArg Fin.val h
  simp only [shellInX, shellOutX, Fin.val_castAdd, T0_val, lo_val, cs1_val] at this
  omega

theorem HF_lo (i : Fin (SD x D D2)) : HF x D D2 Dv DL (lo i) = hK x D 0 D2 i := by
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hJ : lo (Dv := Dv) (DL := DL) i ≠ TJ x D D2 Dv DL := by
    intro e
    have := congrArg Fin.val e
    rw [lo_val, TJ_val] at this
    have := i.isLt
    omega
  unfold HF hK
  by_cases hi : i = kT
  · subst hi
    exact (if_pos rfl).trans (if_pos rfl).symm
  · have hne : lo (Dv := Dv) (DL := DL) i ≠ TK x D D2 Dv DL := fun e => hi (lo_inj e)
    rw [if_neg hne, if_neg hJ, if_neg hi]

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellX
