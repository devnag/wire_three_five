import Proof.Packets.SrcStartPoolGen
import Proof.Packets.SrcStartStream
import Proof.PCP.ProjectionNormalizationField
import Proof.Packets.PacketsSetupWords
import Proof.Packets.PacketsMetaMaps

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Stages
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. Generic: pad, dock, mask -/

theorem pad_nil (R : ℕ) : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by
  simp [ZeroPadding.pad]

/-- A heads-`0` run, padded to `R` and docked. -/
theorem stage0 {U n s : ℕ} {M : Machine n s} {c : ℕ} {tin tout : Fin n → List Bool}
    (h : Step M c (fun _ => 0) tin (fun _ => 0) tout) (σ : Fin n → Fin U) (hσ : Function.Injective σ) (R : ℕ)
    (E : Fin U → List Bool) (hE : ∀ j, E (σ j) = ZeroPadding.pad R (tin j)) :
    Step (RecoveryFocus.machine σ M) c (fun _ => 0) E (fun _ => 0) (install σ E (fun j => ZeroPadding.pad R (tout j))) := by
  have d := (h.pad (fun _ => R)).dock σ hσ (fun _ => 0) E (fun _ => rfl) hE
  exact d.congr (dockH_existing σ _ _ (fun _ => rfl)) rfl

/-- `MaskedReset` with every head selected: heads `0` at both ends. -/
theorem mask0 {n s : ℕ} {M : Machine n s} {c : ℕ} {tin tout : Fin n → List Bool} {H : Fin n → ℕ}
    (h : Step M c (fun _ => 0) tin H tout) :
    ∃ k, Step (MaskedReset.machine M (fun _ => true)) (2*c+2) (fun _ => 0) (Fin.addCases tin (fun _ : Fin 1 => []))
      (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate k false)) := by
  obtain ⟨k, hm⟩ := PacketsGlue.RequestMeta.step_mask0 h (fun _ => true) (fun _ _ => rfl)
  refine ⟨k, (hm.congr_in ?_ rfl).congr ?_ rfl⟩
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem vec2_zero : (![0, 0] : Fin 2 → ℕ) = fun _ => 0 := by
  funext i; fin_cases i <;> rfl

/-- **A two-tape stage, masked and docked** onto `xs` (source, kept), `xo` (target, blank at entry), `xl` (the log, blank). -/
theorem pair_stage {U s : ℕ} {M : Machine 2 s} {c : ℕ} {src out : List Bool} {H : Fin 2 → ℕ}
    (h : Step M c (fun _ => 0) ![src, []] H ![src, out]) (R : ℕ) (xs xo xl : Fin U)
    (h1 : xs ≠ xo) (h2 : xs ≠ xl) (h3 : xo ≠ xl) (E : Fin U → List Bool)
    (hs : E xs = ZeroPadding.pad R src) (ho : E xo = List.replicate R false) (hl : E xl = List.replicate R false) :
    ∃ E' : Fin U → List Bool,
      Step (RecoveryFocus.machine ![xs, xo, xl] (MaskedReset.machine M (fun _ => true))) (2*c+2) (fun _ => 0) E (fun _ => 0) E' ∧
      E' xs = E xs ∧ E' xo = ZeroPadding.pad R out ∧ ∀ x, x ≠ xo → x ≠ xl → E' x = E x := by
  obtain ⟨k, hm⟩ := mask0 h
  have hinj : Function.Injective (![xs, xo, xl] : Fin 3 → Fin U) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have st := stage0 hm (![xs, xo, xl] : Fin 3 → Fin U) hinj R E (by
    intro j
    fin_cases j
    · exact hs
    · show E xo = ZeroPadding.pad R ([] : List Bool)
      rw [ho, pad_nil]
    · show E xl = ZeroPadding.pad R ([] : List Bool)
      rw [hl, pad_nil])
  refine ⟨_, st, ?_, ?_, ?_⟩
  · have e : install (![xs, xo, xl] : Fin 3 → Fin U) E
        (fun j => ZeroPadding.pad R (Fin.addCases (![src, out] : Fin 2 → List Bool) (fun _ : Fin 1 => List.replicate k false) j)) xs =
        ZeroPadding.pad R src := install_slot (![xs, xo, xl] : Fin 3 → Fin U) hinj E _ 0
    rw [e, hs]
  · exact install_slot (![xs, xo, xl] : Fin 3 → Fin U) hinj E
      (fun j => ZeroPadding.pad R (Fin.addCases (![src, out] : Fin 2 → List Bool) (fun _ : Fin 1 => List.replicate k false) j)) 1
  · intro x hxo hxl
    by_cases hxs : x = xs
    · subst hxs
      have e : install (![x, xo, xl] : Fin 3 → Fin U) E
          (fun j => ZeroPadding.pad R (Fin.addCases (![src, out] : Fin 2 → List Bool) (fun _ : Fin 1 => List.replicate k false) j)) x =
          ZeroPadding.pad R src := install_slot (![x, xo, xl] : Fin 3 → Fin U) hinj E _ 0
      rw [e, hs]
    · apply install_other
      intro j hj
      fin_cases j
      · exact hxs hj.symm
      · exact hxo hj.symm
      · exact hxl hj.symm

/-! ## 2. The local two-tape runs -/

/-- The frame copier: `frame w` is copied verbatim onto the blank target; the source is kept. -/
theorem field_local (w : List Bool) : ∃ H, Step RepairSource.ProjectionNormalization.Field.machine (2*w.length+1) (fun _ => 0)
    ![RepairOrdinary.frame w, []] H ![RepairOrdinary.frame w, RepairOrdinary.frame w] := by
  obtain ⟨r, hr, hf, _⟩ := RepairSource.ProjectionNormalization.Field.copy_run [] w [] []
  refine ⟨_, Step.of_run (hin := fun _ => 0) (tin := ![RepairOrdinary.frame w, []]) ?_ (by rw [hf]) ?_⟩
  · have e : (⟨RepairSource.ProjectionNormalization.Field.machine.start, (fun _ => 0), ![RepairOrdinary.frame w, []]⟩ :
        Configuration 2 3) = RepairSource.ProjectionNormalization.Field.cfg 0 ([] ++ RepairOrdinary.frame w ++ []) ([] : List Bool).length [] := by
      simp only [RepairSource.ProjectionNormalization.Field.cfg, List.nil_append, List.append_nil, List.length_nil]
      rw [← vec2_zero]
      rfl
    rw [e]; exact hr
  · rw [hf]
    simp [RepairSource.ProjectionNormalization.Field.cfg]

/-- The unframer: `frame w ↦ w` onto the blank target; the source is kept. -/
theorem unframe_local (w : List Bool) : ∃ H, Step GeneratedAmplifier.Copy.machine (2*w.length+1) (fun _ => 0)
    ![RepairOrdinary.frame w, []] H ![RepairOrdinary.frame w, w] := by
  have h := NearCubicWires.SourceStart.Circuit.unframe_step [] w [] []
  simp only [List.nil_append, List.append_nil, List.length_nil] at h
  refine ⟨_, h.congr_in ?_ rfl⟩
  funext i; fin_cases i <;> rfl

/-- `1^n ↦ CompareMachine.word n`; the source is kept. -/
theorem cmp_local (n : ℕ) : ∃ H, Step PacketsGlue.CmpWord.machine (n+2) (fun _ => 0)
    ![List.replicate n true, []] H ![List.replicate n true, CompareMachine.word n] := by
  obtain ⟨H, h⟩ := PacketsGlue.CmpWord.run n
  exact ⟨H, h.congr_in vec2_zero rfl⟩

/-- The unary copier `1^n ↦ 1^n`; the source is kept. -/
theorem copy_local (n : ℕ) : ∃ H, Step (PacketsGlue.RequestMeta.CopyPlus.machine 0) (n+1+0) (fun _ => 0)
    ![List.replicate n true, []] H ![List.replicate n true, List.replicate n true] := by
  have h := PacketsGlue.RequestMeta.CopyPlus.run 0 n
  exact ⟨_, h.congr_in vec2_zero rfl⟩

/-- The frame counter: `frame (frames xs) ↦ 1^|xs|`; the source is kept. -/
theorem count_local (xs : List (List Bool)) : ∃ H, Step PacketsGlue.CountFrames.machine
    (RepairOrdinary.frame (PacketsGlue.CountFrames.frames xs)).length (fun _ => 0)
    ![RepairOrdinary.frame (PacketsGlue.CountFrames.frames xs), []] H
    ![RepairOrdinary.frame (PacketsGlue.CountFrames.frames xs), List.replicate xs.length true] := by
  have h := PacketsGlue.RequestMeta.countFrames_step xs
  exact ⟨_, h.congr_in vec2_zero rfl⟩

end
end NearCubicWires.SourceStart.Stages

