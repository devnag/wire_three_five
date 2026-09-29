import Proof.CaseAnalysis.FinalSelectorCellSetter
import Proof.CaseAnalysis.RowsEstimatorPad

/-! A.4 cold start, part 5: the LOADER, first group of ports.

Working down the port chart of `RepairCloseoutFinalSelectorColdPorts`, this
file physically writes the three seed masks (ports 1, 2, 3) and the two
single-cell scalars (ports 29, 32) of the selector's 35-tape entry bank.
Every stage is an accepted worker docked by `RecoveryFocus`; the only newly
built machine in the whole group is the one-cell writer `setOne`.

The bank is `Fin 96`: the selector's 36 tapes at 0-35, the paid drivers at
36-40, and per-group scratch above that (this group owns 41-44).  The group
is stated over an ARBITRARY ambient bank `A` satisfying `MaskReady`, and
returns `mask_untouched`: every other selector tape is left exactly as it
was.  That is what lets the groups be sequenced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The `ClockJoin` flavour of a heads-at-zero receipt. -/
theorem step_of_clock {t s n : ℕ} {p : Machine t s} {inp out : Fin t→List Bool}
    (h:ClockJoin.ReadyRun p n inp out):Step p n (fun _=>0) inp (fun _=>0) out:=by
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  refine ⟨r,?_,funext hh,ht,hs⟩
  change run p n inp=some r at hr
  exact hr

/-! ### Slot maps -/



/-! ### Worker receipts, all heads at zero -/


/-! ### The banks after each docked stage -/



/-! ### Stage entry ports -/


/-! ### The docked stages -/




/-! ### The group receipt -/

end NearCubicWires.RepairOrdinary.CloseoutFinalSelector
