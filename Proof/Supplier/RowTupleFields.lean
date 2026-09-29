import Proof.Supplier.RowTupleLogs

/-! Write the three initial zero fields from the two paid unary widths.
All normalizer flags and scratch start empty; only width/bound/degree/limit
metadata are supplied to this cold prefix. -/
namespace NearCubicWires.RepairOrdinary.RowTupleColdFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 3) : Fin 5→Fin 29 :=
  ![![18,19,1,20,21],![18,22,6,23,24],![25,26,0,27,28]] j
noncomputable def part (j : Fin 3) := RecoveryFocus.machine (slots j) ClockNormalize.machine
noncomputable def first := Composition.machine (part 0) (part 1)
noncomputable def machine := Composition.machine first (part 2)

theorem zero_ready (w : ℕ) : ∃ out,
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockScalarFields.zeroInput w) out ∧
      out 0=List.replicate w true ∧ out 2=frame (binary w 0) := by
  obtain ⟨r,hr,h0,_,h2,_,_,hh,hs⟩ := ClockScalarFields.zero_run w
  exact ⟨r.final.tapes,⟨r,hr,rfl,hh,hs.le⟩,h0,h2⟩

end NearCubicWires.RepairOrdinary.RowTupleColdFields
