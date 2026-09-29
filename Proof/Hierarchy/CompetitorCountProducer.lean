import Proof.Hierarchy.CompetitorCountEntry

/-! Actual whole count producer from raw cells, physical native/scalar widths
and the physical cell-count word. All work tapes initially are blank. A paid
zero-scalar constructor feeds the sequential count loop; its scratch is reused.
Producing the three dimension words is the enclosing matrix caller's work. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountProducer
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b w : ℕ) (xs : List ℕ) : Fin 11 → List Bool :=
  fun i => match i.val with
    | 0 => CompetitorCountFold.raw b xs
    | 1 => List.replicate b true
    | 2 => List.replicate w true
    | 8 => CompareMachine.word xs.length
    | _ => []
def zeroSlots : Fin 5 → Fin 11 := ![2,10,5,9,4]
noncomputable def zeroProgram := RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def foldProgram := TapeEmbedding.machine 2 CompetitorCountEntry.machine
noncomputable def machine := Composition.machine zeroProgram foldProgram
def budget (w n : ℕ) := n*(16*w+20)+4*w+10

theorem zero_ready (b w : ℕ) (xs : List ℕ) :
    ∃ out,ClockJoin.ReadyRun zeroProgram (4*w+4) (input b w xs) out ∧
      (∀ i : Fin 9,out (i.castAdd 2)=CompetitorCountEntry.input b w xs i) := by
  obtain ⟨r,hr,h0,_,h2,_,h4,hh,hs⟩ := ClockScalarFields.zero_run w
  have hready : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (ClockScalarFields.zeroInput w) r.final.tapes :=
    ⟨r,hr,rfl,hh,hs.le⟩
  have hfocus := CompetitorRationalProducts.bounded_focus zeroSlots (by decide) _ _ _ hready (input b w xs)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨install zeroSlots (input b w xs) r.final.tapes,hfocus,?_⟩
  intro i; fin_cases i
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact (install_slot zeroSlots (by decide) _ _ 0).trans h0
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact (install_slot zeroSlots (by decide) _ _ 4).trans h4
  · exact (install_slot zeroSlots (by decide) _ _ 2).trans h2
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)
  · exact install_other zeroSlots _ _ _ (by decide)

end NearCubicWires.RepairOrdinary.CompetitorCountProducer
