import Proof.CaseAnalysis.FinalSupplierCountStage
import Proof.CaseAnalysis.RowsProjectionReset

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank bankAt)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **The zeroed tape IS the padded empty tape.**  `RecoveryScratchErase`'s exit
shape and `ZeroPadding`'s padding are the same list. -/
theorem pad_nil (total : ℕ) : ZeroPadding.pad total [] = List.replicate total false := rfl

/-! ## §2  The band, and the fictional bank the docks are run in

`install slots A (fun _ => [])` (`Proof/Amplification/RecoveryReadyCalls.lean`) is the bank
in which the round's slots are literally empty.  Every docked engine applies to
it with NO hypothesis on `A` at all.  `bandCap` pads exactly those slots back up
to the real, zeroed band, and pads nothing else. -/

/-- **The `k`-FREE band invariant.**  Contrast APPENDS's
`fun k s => BlankFrom (line + k * block) s`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`), whose line MOVES and which
`band_exhausted` (`Proof/CaseAnalysis/FinalPrologueBlankBand.lean`) therefore
exhausts.  `line` here does not depend on the round index. -/
def ZeroBand (total line : ℕ) (s : ℕ → List Bool) : Prop :=
  ∀ v : ℕ, line ≤ v → s v = List.replicate total false

/-! ## §3  The deliverable: one round of the loop, over a RECYCLED band -/

/-! ## §4  The band is restored, and the length bound that lets it be -/

/-! ## §5  The two disciplines, side by side

`band_exhausted` (`Proof/CaseAnalysis/FinalPrologueBlankBand.lean`) is about a
line that MOVES: `line + k * block` eventually reaches the bank width, and past
that the invariant is the vacuous one of
`blankFrom_above_bank_certifies_nothing` (`:244`).  `ZeroBand` is stated at a
line that does not move.  The two statements below are the arithmetic INVZERO
left open, in the form that decides it. -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle
