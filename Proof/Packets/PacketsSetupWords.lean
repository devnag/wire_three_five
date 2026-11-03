import Proof.Packets.PacketsFieldWidth
import Proof.MachineModel.ClockScalarFields
import Proof.PCP.VerifierDecodingCompare

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.FrameUnary
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- Tape 0 `1^b`, tape 1 the output `frame (1^b)`. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q x =>
    if q.val = 0 then some (if x 0 then ⟨1, ![none, some true], ![.stay, .right]⟩
      else ⟨2, ![none, some false], ![.stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, some true], ![.right, .right]⟩
    else none

end NearCubicWires.PacketsGlue.FrameUnary

namespace NearCubicWires.PacketsGlue.CmpWord
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- Tape 0 `1^n`, tape 1 the output `false :: 1^n`. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q x =>
    if q.val = 0 then some ⟨1, ![none, some false], ![.stay, .right]⟩
    else if q.val = 1 then some (if x 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, none], ![.stay, .stay]⟩)
    else none

def cfg (q : Fin 3) (n i : ℕ) (o : List Bool) (ho : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, ho], ![List.replicate n true, o]⟩

theorem s0 (n : ℕ) : step machine (cfg 0 n 0 [] 0) = some (cfg 1 n 0 [false] 1) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem s1t (n i : ℕ) (hi : i < n) : step machine (cfg 1 n i (false :: List.replicate i true) (i + 1)) =
    some (cfg 1 n (i + 1) (false :: List.replicate (i + 1) true) (i + 1 + 1)) := by
  have hr : readTapeBit (List.replicate n true) i = true := read_replicate_true n i hi
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · have h1 : writeTapeBit (false :: List.replicate i true) (i + 1) true = false :: List.replicate (i + 1) true := by
      have := Streaming.write_append (false :: List.replicate i true) true
      simp only [List.length_cons, List.length_replicate] at this
      rw [this, List.replicate_succ']; rfl
    funext k; fin_cases k
    · simp [applyAction]
    · simp only [applyAction]
      simp [h1]

theorem s1f (n : ℕ) : step machine (cfg 1 n n (false :: List.replicate n true) (n + 1)) =
    some (cfg 2 n n (false :: List.replicate n true) (n + 1)) := by
  have hr : readTapeBit (List.replicate n true) n = false := read_replicate_end n true
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem loop (n : ℕ) : ∀ i, i ≤ n →
    Timed machine (n - i) (cfg 1 n i (false :: List.replicate i true) (i + 1))
      (cfg 1 n n (false :: List.replicate n true) (n + 1)) := by
  intro i hi
  induction h : n - i generalizing i with
  | zero =>
    have : i = n := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s1t n i (by omega))
    have t2 := ih (i + 1) (by omega) (by omega)
    have t := t1.trans t2
    rw [show 1 + k = k + 1 by omega] at t
    exact t

theorem run (n : ℕ) : ∃ H, Step machine (n + 2) ![0, 0] ![List.replicate n true, []] H
    ![List.replicate n true, false :: List.replicate n true] := by
  have t0 := Timed.single (p := machine) (by simp [machine, cfg]) (s0 n)
  have t1 := loop n 0 (by omega)
  have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s1f n)
  obtain ⟨r, hr, hf, hs⟩ := ((t0.trans t1).trans t2).run (by simp [machine, cfg])
  refine ⟨_, r, ?_, rfl, ?_, by omega⟩
  · have hc : (⟨machine.start, ![0, 0], ![List.replicate n true, []]⟩ : Configuration 2 3) = cfg 0 n 0 [] 0 := rfl
    rw [hc]
    have e : 1 + (n - 0) + 1 = n + 2 := by omega
    rw [e] at hr
    simpa using hr
  · rw [hf]; rfl

end NearCubicWires.PacketsGlue.CmpWord

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

/-! ## Renaming the output tape of a word map -/

/-! ## The zero digit word -/

/-! ## The zero test -/

/-! ## Two-argument word maps and `pairW` -/

/-! ## The flag word `frame (binary W b)` for `b ≤ 1` -/



/-! ## The row-count driver word -/

end
end NearCubicWires.PacketsGlue.RequestMeta

