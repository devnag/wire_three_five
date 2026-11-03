import Proof.Packets.PacketsRoot
import Proof.MachineModel.BlockScrubEntry
import Proof.Circuits.DecompositionCountPosition

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-! ## The counter stamp -/

namespace NearCubicWires.PacketsGlue
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary.RecoveryExecution

end NearCubicWires.PacketsGlue

namespace NearCubicWires.PacketsGlue.Stamp
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (sentC read_sent write_sent read_rep)

/-- Tape 0: the unary source `1^m`; tapes `1..k+1`: the counters. -/
def machine (k : ℕ) : Machine (2 + k) 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then some ⟨1, fun i => if i.val = 0 then none else some false,
        fun i => if i.val = 0 then .stay else .right⟩
    else if q.val = 1 then (if b ⟨0, by omega⟩ then
        some ⟨1, fun i => if i.val = 0 then none else some true, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .left⟩)
    else if q.val = 2 then (if b ⟨1, by omega⟩ then some ⟨2, fun _ => none, fun _ => .left⟩
      else some ⟨3, fun _ => none, fun _ => .stay⟩)
    else none

/-- All counters share one content and one head. -/
def cfg (k : ℕ) (q : Fin 4) (m uh : ℕ) (C : List Bool) (ch : ℕ) : Configuration (2 + k) 4 :=
  ⟨q, fun i => if i.val = 0 then uh else ch, fun i => if i.val = 0 then List.replicate m true else C⟩

section Steps
variable (k m uh : ℕ) (C : List Bool) (ch : ℕ)

theorem s0 : step (machine k) (cfg k 0 m uh C ch) = some (cfg k 1 m uh (writeTapeBit C ch false) (ch + 1)) := by
  simp only [step, machine, cfg]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s1t (h : readTapeBit (List.replicate m true) uh = true) :
    step (machine k) (cfg k 1 m uh C ch) = some (cfg k 1 m (uh + 1) (writeTapeBit C ch true) (ch + 1)) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((1 : Fin 4).val = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s1f (h : readTapeBit (List.replicate m true) uh = false) :
    step (machine k) (cfg k 1 m uh C ch) = some (cfg k 2 m (uh - 1) C (ch - 1)) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((1 : Fin 4).val = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s2t (h : readTapeBit C ch = true) :
    step (machine k) (cfg k 2 m uh C ch) = some (cfg k 2 m (uh - 1) C (ch - 1)) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((2 : Fin 4).val = 0) from by decide, show ¬ ((2 : Fin 4).val = 1) from by decide,
    show ¬ ((1 : ℕ) = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

theorem s2f (h : readTapeBit C ch = false) :
    step (machine k) (cfg k 2 m uh C ch) = some (cfg k 3 m uh C ch) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp only [Fin.isValue, show ¬ ((2 : Fin 4).val = 0) from by decide, show ¬ ((2 : Fin 4).val = 1) from by decide,
    show ¬ ((1 : ℕ) = 0) from by decide, if_false, if_true, h]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, HeadMove.apply, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, HeadMove.apply, hi']
  · funext i
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext (by simpa using hi)
      simp [applyAction, hi']
    · have hi' : i ≠ 0 := fun h => hi (by rw [h]; rfl)
      simp [applyAction, hi']

end Steps

theorem fill (k m : ℕ) : ∀ t j : ℕ, j + t = m →
    Timed (machine k) t (cfg k 1 m j (sentC j) (j + 1)) (cfg k 1 m m (sentC m) (m + 1)) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = m by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h : readTapeBit (List.replicate m true) j = true := by rw [read_rep]; simp; omega
    have t1 := Timed.single (p := machine k) (by rfl) (s1t k m j (sentC j) (j + 1) h)
    rw [write_sent] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

theorem rewind (k m : ℕ) : ∀ p : ℕ, p ≤ m →
    Timed (machine k) (p + 1) (cfg k 2 m (p - 1) (sentC m) p) (cfg k 3 m 0 (sentC m) 0) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sentC m) 0 = false := rfl
    simpa using Timed.single (p := machine k) (by rfl) (s2f k m (0 - 1) (sentC m) 0 h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sentC m) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine k) (by rfl) (s2t k m (p + 1 - 1) (sentC m) (p + 1) h)
    rw [show p + 1 - 1 - 1 = p - 1 by omega, show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

/-- **The stamp**: `k+1` counters `word m`, the source kept, all heads `0`, in `2m + 3` steps. -/
theorem run (k m : ℕ) :
    Step (machine k) (2 * m + 3) (fun _ => 0) (fun i => if i.val = 0 then List.replicate m true else [])
      (fun _ => 0)
      (fun i => if i.val = 0 then List.replicate m true else RepairSource.VerifierDecoding.CompareMachine.word m) := by
  have t0 := Timed.single (p := machine k) (by rfl) (s0 k m 0 [] 0)
  have e0 : writeTapeBit ([] : List Bool) 0 false = sentC 0 := rfl
  rw [e0] at t0
  have t1 := fill k m m 0 (by omega)
  have hf : readTapeBit (List.replicate m true) m = false := by rw [read_rep]; simp
  have t2 := Timed.single (p := machine k) (by rfl) (s1f k m m (sentC m) (m + 1) hf)
  have t3 := rewind k m m (le_refl _)
  rw [show m + 1 - 1 = m by omega] at t2
  have e := ((t0.trans t1).trans t2).trans t3
  have s := NatAt.Timed.toStep e rfl rfl
  have hh0 : (cfg k 0 m 0 [] 0).heads = fun _ => 0 := by funext i; simp [cfg]
  have hh3 : (cfg k 3 m 0 (sentC m) 0).heads = fun _ => 0 := by funext i; simp [cfg]
  rw [hh0, hh3, show 0 + 1 + m + 1 + (m + 1) = 2 * m + 3 by omega] at s
  exact s

end NearCubicWires.PacketsGlue.Stamp

/-! ## Write `c` trues -/

namespace NearCubicWires.PacketsGlue.WriteC
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

end NearCubicWires.PacketsGlue.WriteC

/-! ## The nest of loops -/

namespace NearCubicWires.PacketsGlue.Nest
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform


end NearCubicWires.PacketsGlue.Nest

/-! ## Drain the log into the driver -/

namespace NearCubicWires.PacketsGlue.Drain
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (sentC read_sent read_rep write_rep)

section Steps

end Steps

end NearCubicWires.PacketsGlue.Drain

