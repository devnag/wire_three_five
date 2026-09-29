import Proof.PCP.ProjectionNormalizationSuffixScan

/-! One paid original-source restoration around the whole later-clause scan.
The source starts at the position immediately following the candidate and
returns to precisely that position; it is never rewound to the global origin. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace CursorRestore

theorem other_forward {t s : ℕ} (p : Machine t s) (target i : Fin t) (hi : i≠target)
    (hp : NoLeft p i) : NoLeft (machine p target) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · by_cases hh : p.halted q=true
    · simp [machine,hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j => bits (j.castAdd 1)) with
      | none => simp [machine,hh,hr] at ha
      | some b =>
        simp [machine,hh,hr] at ha
        subst a
        simpa only [recordAction,Fin.addCases_left] using hp q (fun j => bits (j.castAdd 1)) b hr
  · simp only [machine,Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha
        simp [MaskedReset.rewindAction,hi]
      · cases ha
        simp [Rewind.finishAction]
    · contradiction

theorem repeat_forward {t s : ℕ} (p : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (i : Fin t) (hp : NoLeft p i) :
    NoLeft (RepeatMachine.machine p accepted) (i.castAdd 1) := by
  intro state bits a ha
  cases hs : (RepeatMachine.code s).symm state with
  | inl q =>
    simp only [RepeatMachine.machine,hs] at ha
    split at ha
    · cases ha
      simp [RepeatMachine.action]
    · cases hr : p.rule q (fun j => bits (j.castAdd 1)) with
      | none => simp [hr] at ha
      | some b =>
        simp only [hr,Option.map_some,Option.some.injEq] at ha
        subst a
        simpa only [RepeatMachine.bodyAction,Fin.addCases_left] using hp q (fun j => bits (j.castAdd 1)) b hr
  | inr q =>
    simp only [RepeatMachine.machine,hs] at ha
    split at ha
    · split at ha <;> cases ha <;> simp [RepeatMachine.action]
    · split at ha
      · cases ha; simp [RepeatMachine.action]
      · split at ha
        · split at ha <;> cases ha <;> simp [RepeatMachine.action]
        · contradiction

end CursorRestore
namespace SuffixRestore


end SuffixRestore
end NearCubicWires.RepairSource.ProjectionNormalization
