import Proof.Wire_3_5.Primitive.Writers.ComposeBase
import Proof.Wire_3_5.Primitive.Writers.AppendFrame
import Proof.CaseAnalysis.FinalWordFunctionDock

/-! # PA.compose.glue: two rewound word functions compose to one ordinary word function

The residual `Glue` of the compose plan (check 62b01809…). `prim:runtime` (P3:3105-3115): the per-call program runs
seed fixing (`w ↦ s`) and then the final pass (`w ++ s ↦ o`); "the running time is the sum". The glue machine, on
`8 + t₁ + t₂` tapes (eight own tapes, then the first and the second machine's tapes):

1. copy `frame w` from tape `0` to the first machine's entry tape (base `FrameCopy` under base `Rewind`);
2. run the first machine SHADOWED (`PrimAsmShadow`): its raw output `s` and the shadow tapes `V, W`;
3. the ruler kernel (`PrimAsmRuler`): `replicate |s| true`;
4. the append kernel (`PrimAsmAppendFrame`): `frame (w ++ s)` on the second machine's entry tape;
5. run the second machine (base `rewound_bank_dock`): `o` on its output tape.

Every stage ends with all heads at `0`; the stages are joined by base `Step.seq`, docked by base `Step.dock`. The cost is
at most `12|w| + 7b₄ + b₅ + 23 ≤ glueK·(|w| + b₄ + b₅ + 1)`.

Paper quantity of the main type: the composed word function `w ↦ o` (`glue : Compose.Glue`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ComposeGlue
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.CloseoutFinal.C10WordFunctionDock

/-! ## Docking helpers -/

theorem dock0 {t u s : ℕ} {p : Machine t s} {n : ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n (fun _ => 0) A (fun _ => 0) (install slots A tout) := by
  have h' := h.dock slots hi (fun _ => 0) A (fun _ => rfl) hA
  rwa [dockH_zero] at h'

theorem inst_at {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (tout : Fin t → List Bool) (j : Fin t) (i : Fin u) (hij : slots j = i) : install slots A tout i = tout j := by
  subst hij
  exact install_slot slots hi A tout j

theorem inst_off {t u : ℕ} (slots : Fin t → Fin u) (A : Fin u → List Bool) (tout : Fin t → List Bool) (i : Fin u)
    (h : ∀ k, (slots k).val ≠ i.val) : install slots A tout i = A i :=
  install_other slots A tout i (fun k hk => h k (congrArg Fin.val hk))

@[simp] theorem inSlot_val (p : Program) : (inSlot p).val = 0 := rfl

/-! ## The layout -/

section Layout
variable (P1 P2 : Program)

/-- Eight own tapes, then the first machine's `t₁` tapes, then the second machine's `t₂` tapes. -/
abbrev NT : ℕ := 8 + P1.tapeCount + P2.tapeCount

/-- Own tape `k < 8`: `0` request, `1` copy counter, `2` copy workspace, `3` V, `4` W, `5` marker, `6` ruler,
`7` append workspace. -/
def tp (k : ℕ) (hk : k < 8) : Fin (NT P1 P2) := ⟨k, by show k < 8 + P1.tapeCount + P2.tapeCount; omega⟩

def b1 (j : Fin P1.tapeCount) : Fin (NT P1 P2) :=
  ⟨8 + j.val, by have := j.isLt; show 8 + j.val < 8 + P1.tapeCount + P2.tapeCount; omega⟩

def b2 (j : Fin P2.tapeCount) : Fin (NT P1 P2) :=
  ⟨8 + P1.tapeCount + j.val, by have := j.isLt; show 8 + P1.tapeCount + j.val < 8 + P1.tapeCount + P2.tapeCount; omega⟩

@[simp] theorem tp_val (k : ℕ) (hk : k < 8) : (tp P1 P2 k hk).val = k := rfl
@[simp] theorem b1_val (j : Fin P1.tapeCount) : (b1 P1 P2 j).val = 8 + j.val := rfl
@[simp] theorem b2_val (j : Fin P2.tapeCount) : (b2 P1 P2 j).val = 8 + P1.tapeCount + j.val := rfl

theorem b2_inj : Function.Injective (b2 P1 P2) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [b2_val] at hv
  exact Fin.ext (by omega)

/-- Stage 1 (copy): request, first entry tape, counter, workspace. -/
def s1 : Fin (3 + 1) → Fin (NT P1 P2) :=
  ![tp P1 P2 0 (by norm_num), b1 P1 P2 (inSlot P1), tp P1 P2 1 (by norm_num), tp P1 P2 2 (by norm_num)]

/-- Stage 2 (shadowed first machine): its tapes, then V and W. -/
def s2 : Fin (P1.tapeCount + 2) → Fin (NT P1 P2) :=
  Fin.addCases (b1 P1 P2) (fun k => if k.val = 0 then tp P1 P2 3 (by norm_num) else tp P1 P2 4 (by norm_num))

/-- Stage 3 (ruler): V, W, marker, ruler. -/
def s3 : Fin 4 → Fin (NT P1 P2) :=
  ![tp P1 P2 3 (by norm_num), tp P1 P2 4 (by norm_num), tp P1 P2 5 (by norm_num), tp P1 P2 6 (by norm_num)]

/-- Stage 4 (append): request, first output tape, ruler, second entry tape, workspace. -/
def s4 : Fin (4 + 1) → Fin (NT P1 P2) :=
  ![tp P1 P2 0 (by norm_num), b1 P1 P2 P1.outputTape, tp P1 P2 6 (by norm_num), b2 P1 P2 (inSlot P2),
    tp P1 P2 7 (by norm_num)]

theorem s1_val (k : Fin (3 + 1)) : (s1 P1 P2 k).val = 0 ∨ (s1 P1 P2 k).val = 8 ∨ (s1 P1 P2 k).val = 1 ∨
    (s1 P1 P2 k).val = 2 := by
  fin_cases k <;> simp [s1]

theorem s2_left (j : Fin P1.tapeCount) : s2 P1 P2 (j.castAdd 2) = b1 P1 P2 j := by simp [s2]

theorem s2_right (k : Fin 2) :
    s2 P1 P2 (k.natAdd P1.tapeCount) = if k.val = 0 then tp P1 P2 3 (by norm_num) else tp P1 P2 4 (by norm_num) := by
  simp [s2]

theorem s2_val (k : Fin (P1.tapeCount + 2)) :
    (8 ≤ (s2 P1 P2 k).val ∧ (s2 P1 P2 k).val < 8 + P1.tapeCount) ∨ (s2 P1 P2 k).val = 3 ∨ (s2 P1 P2 k).val = 4 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · rw [s2_left]; left; simp only [b1_val]; have := j.isLt; omega
  · rw [s2_right]; split_ifs <;> simp

theorem s3_val (k : Fin 4) : 3 ≤ (s3 P1 P2 k).val ∧ (s3 P1 P2 k).val ≤ 6 := by
  fin_cases k <;> simp [s3]

theorem s4_val (k : Fin (4 + 1)) : (s4 P1 P2 k).val = 0 ∨ (s4 P1 P2 k).val = 8 + P1.outputTape.val ∨
    (s4 P1 P2 k).val = 6 ∨ (s4 P1 P2 k).val = 8 + P1.tapeCount ∨ (s4 P1 P2 k).val = 7 := by
  fin_cases k <;> simp [s4]

theorem s1_inj : Function.Injective (s1 P1 P2) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [s1] at hv ⊢

theorem s2_inj : Function.Injective (s2 P1 P2) := by
  intro a b
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a <;> refine Fin.addCases (fun b' => ?_) (fun b' => ?_) b <;>
    intro h <;> have hv := congrArg Fin.val h <;> have ha := a'.isLt <;> have hb := b'.isLt
  · rw [s2_left, s2_left] at hv; simp only [b1_val] at hv; ext; simp; omega
  · rw [s2_left, s2_right] at hv; simp only [b1_val] at hv; split_ifs at hv <;> simp at hv <;> omega
  · rw [s2_right, s2_left] at hv; simp only [b1_val] at hv; split_ifs at hv <;> simp at hv <;> omega
  · rw [s2_right, s2_right] at hv
    ext
    simp only [Fin.val_natAdd]
    split_ifs at hv with h1 h2 h2 <;> simp at hv <;> omega

theorem s3_inj : Function.Injective (s3 P1 P2) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [s3] at hv ⊢

theorem s4_inj : Function.Injective (s4 P1 P2) := by
  intro a b h
  have hv := congrArg Fin.val h
  have ho := P1.outputTape.isLt
  fin_cases a <;> fin_cases b <;> simp [s4] at hv ⊢ <;> omega

/-- The glue's entry bank: the framed request on tape `0`. -/
def A0 (x : List Bool) : Fin (NT P1 P2) → List Bool := fun i => if i.val = 0 then x else []

/-- **The glue machine.** -/
noncomputable def gmachine : Machine (NT P1 P2) ((((5 + 2) + P1.stateCount) + 5) + (5 + 2) + P2.stateCount) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (s1 P1 P2) (Rewind.machine FrameCopy.machine))
    (RecoveryFocus.machine (s2 P1 P2) (Shadow.machine P1.outputTape P1.machine)))
    (RecoveryFocus.machine (s3 P1 P2) Ruler.machine))
    (RecoveryFocus.machine (s4 P1 P2) (Rewind.machine AppendFrame.raw)))
    (RecoveryFocus.machine (b2 P1 P2) P2.machine)

/-- The glue's program: output on the second machine's output tape. -/
noncomputable def gprogram : Program where
  tapeCount := NT P1 P2
  stateCount := (((5 + 2) + P1.stateCount) + 5) + (5 + 2) + P2.stateCount
  twoTapes := by show 2 ≤ 8 + P1.tapeCount + P2.tapeCount; omega
  machine := gmachine P1 P2
  outputTape := b2 P1 P2 P2.outputTape
  outputFresh := by simp only [b2_val]; omega

end Layout

/-! ## The run -/

/-- Tape-index arithmetic of the layout. -/
local macro "vt" : tactic =>
  `(tactic| (simp only [ComposeGlue.b1_val, ComposeGlue.tp_val, ComposeGlue.b2_val, ComposeGlue.inSlot_val] <;> omega))

/-- **The glue's run at one request**: from the framed request, the output `o r` on the output tape, within
`12|w| + 7b₄ + b₅ + 23` transitions. -/
theorem glue_run {Req : Type} {w s o : Req → List Bool} {b4 b5 : Req → ℕ}
    (wf1 : RewoundWordFunction Req w s b4) (wf2 : RewoundWordFunction Req (fun r => w r ++ s r) o b5) (r : Req) :
    ∃ (F : ℕ) (A5 : Fin (NT wf1.program wf2.program) → List Bool),
      Step (gmachine wf1.program wf2.program) F (fun _ => 0) (A0 wf1.program wf2.program (frame (w r)))
        (fun _ => 0) A5 ∧
      A5 (b2 wf1.program wf2.program wf2.program.outputTape) = o r ∧
      F ≤ 12 * (w r).length + 7 * b4 r + b5 r + 23 := by
  have ht1 := wf1.program.twoTapes
  have ho1 := wf1.program.outputTape.isLt
  have hof := wf1.program.outputFresh
  -- stage 1: copy the request
  obtain ⟨tout1, h1l, ht10, ht11⟩ := AppendFrame.copy_step (w r)
  have h1 := dock0 h1l (s1 wf1.program wf2.program) (s1_inj _ _) (A0 wf1.program wf2.program (frame (w r))) (by
    intro k
    fin_cases k
    · show (if (0 : ℕ) = 0 then frame (w r) else []) = frame (w r); simp
    · show (if 8 + 0 = 0 then frame (w r) else []) = []; simp
    · show (if (1 : ℕ) = 0 then frame (w r) else []) = []; simp
    · show (if (2 : ℕ) = 0 then frame (w r) else []) = []; simp)
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = install (s1 wf1.program wf2.program) (A0 wf1.program wf2.program (frame (w r))) tout1 :=
    ⟨_, rfl⟩
  rw [← hA1] at h1
  have hA1_in : A1 (tp wf1.program wf2.program 0 (by norm_num)) = frame (w r) := by
    rw [hA1, inst_at _ (s1_inj _ _) _ _ 0 (tp wf1.program wf2.program 0 (by norm_num)) rfl, ht10]
  have hA1_x : A1 (b1 wf1.program wf2.program (inSlot wf1.program)) = frame (w r) := by
    rw [hA1, inst_at _ (s1_inj _ _) _ _ 1 (b1 wf1.program wf2.program (inSlot wf1.program)) rfl, ht11]
  have hA1_off : ∀ i : Fin (NT wf1.program wf2.program), i.val ≠ 0 → i.val ≠ 8 → i.val ≠ 1 → i.val ≠ 2 → A1 i = [] := by
    intro i h0 h8 h1' h2
    rw [hA1, inst_off]
    · simp [A0, h0]
    · intro k; rcases s1_val wf1.program wf2.program k with h | h | h | h <;> omega
  -- stage 2: the first machine, shadowed
  obtain ⟨touts, hts, h2w⟩ := step_of_rewound wf1 r
  have hin0 : wf1.program.inputTapes (w r) wf1.program.outputTape = [] := by
    simp [Program.inputTapes, hof]
  obtain ⟨m, W, h2l, hWl, hWm, hmb, hlast⟩ := Shadow.step_shadow _ _ h2w hin0
  have h2 := dock0 h2l (s2 wf1.program wf2.program) (s2_inj _ _) A1 (by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun k => ?_) j
    · rw [s2_left, Fin.addCases_left]
      by_cases hj : j'.val = 0
      · have he : j' = inSlot wf1.program := Fin.ext hj
        subst he
        rw [hA1_x]
        simp [Program.inputTapes]
      · rw [hA1_off _ (by vt) (by vt) (by vt) (by vt)]
        simp [Program.inputTapes, hj]
    · rw [s2_right, Fin.addCases_right]
      split_ifs <;> exact hA1_off _ (by vt) (by vt) (by vt) (by vt))
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install (s2 wf1.program wf2.program) A1
      (Fin.addCases touts (Shadow.shadowTapes (List.replicate m true) W)) := ⟨_, rfl⟩
  rw [← hA2] at h2
  have hA2_V : A2 (tp wf1.program wf2.program 3 (by norm_num)) = List.replicate m true := by
    rw [hA2, inst_at _ (s2_inj _ _) _ _ ((0 : Fin 2).natAdd _) (tp wf1.program wf2.program 3 (by norm_num))
      (by rw [s2_right]; simp), Fin.addCases_right]
    simp [Shadow.shadowTapes]
  have hA2_W : A2 (tp wf1.program wf2.program 4 (by norm_num)) = W := by
    rw [hA2, inst_at _ (s2_inj _ _) _ _ ((1 : Fin 2).natAdd _) (tp wf1.program wf2.program 4 (by norm_num))
      (by rw [s2_right]; simp), Fin.addCases_right]
    simp [Shadow.shadowTapes]
  have hA2_s : A2 (b1 wf1.program wf2.program wf1.program.outputTape) = s r := by
    rw [hA2, inst_at _ (s2_inj _ _) _ _ (wf1.program.outputTape.castAdd 2)
      (b1 wf1.program wf2.program wf1.program.outputTape) (s2_left _ _ _), Fin.addCases_left, hts]
  have hA2_off : ∀ i : Fin (NT wf1.program wf2.program), (i.val < 8 → i.val ≠ 3 ∧ i.val ≠ 4) →
      (8 ≤ i.val → 8 + wf1.program.tapeCount ≤ i.val) → A2 i = A1 i := by
    intro i hlo hhi
    rw [hA2, inst_off]
    intro k
    rcases s2_val wf1.program wf2.program k with h | h | h <;> omega
  -- stage 3: the ruler
  have h3l := Ruler.ruler_step m W hWm hlast
  have h3 := dock0 h3l (s3 wf1.program wf2.program) (s3_inj _ _) A2 (by
    intro k
    fin_cases k
    · exact hA2_V
    · exact hA2_W
    · show A2 (tp wf1.program wf2.program 5 (by norm_num)) = []
      rw [hA2_off _ (by vt) (by vt)]
      exact hA1_off _ (by vt) (by vt) (by vt) (by vt)
    · show A2 (tp wf1.program wf2.program 6 (by norm_num)) = []
      rw [hA2_off _ (by vt) (by vt)]
      exact hA1_off _ (by vt) (by vt) (by vt) (by vt))
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = install (s3 wf1.program wf2.program) A2
      ![List.replicate m true, W, [true], List.replicate W.length true] := ⟨_, rfl⟩
  rw [← hA3] at h3
  have hA3_R : A3 (tp wf1.program wf2.program 6 (by norm_num)) = List.replicate (s r).length true := by
    rw [hA3, inst_at _ (s3_inj _ _) _ _ 3 (tp wf1.program wf2.program 6 (by norm_num)) rfl, hWl, hts]
    rfl
  have hA3_off : ∀ i : Fin (NT wf1.program wf2.program), (i.val < 3 ∨ 6 < i.val) → A3 i = A2 i := by
    intro i hi
    rw [hA3, inst_off]
    intro k
    have := s3_val wf1.program wf2.program k
    omega
  -- stage 4: frame (w ++ s)
  obtain ⟨tout4, h4l, ht43⟩ := AppendFrame.append_step (w r) (s r)
  have h4 := dock0 h4l (s4 wf1.program wf2.program) (s4_inj _ _) A3 (by
    intro k
    fin_cases k
    · show A3 (tp wf1.program wf2.program 0 (by norm_num)) = frame (w r)
      rw [hA3_off _ (by vt), hA2_off _ (by vt) (by vt)]
      exact hA1_in
    · show A3 (b1 wf1.program wf2.program wf1.program.outputTape) = s r
      rw [hA3_off _ (by vt), hA2_s]
    · exact hA3_R
    · show A3 (b2 wf1.program wf2.program (inSlot wf2.program)) = []
      rw [hA3_off _ (by vt), hA2_off _ (by vt) (by vt)]
      exact hA1_off _ (by vt) (by vt) (by vt) (by vt)
    · show A3 (tp wf1.program wf2.program 7 (by norm_num)) = []
      rw [hA3_off _ (by vt), hA2_off _ (by vt) (by vt)]
      exact hA1_off _ (by vt) (by vt) (by vt) (by vt))
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = install (s4 wf1.program wf2.program) A3 tout4 := ⟨_, rfl⟩
  rw [← hA4] at h4
  have hA4_in : A4 (b2 wf1.program wf2.program (inSlot wf2.program)) = frame (w r ++ s r) := by
    rw [hA4, inst_at _ (s4_inj _ _) _ _ 3 (b2 wf1.program wf2.program (inSlot wf2.program)) rfl, ht43]
  have hA4_blank : ∀ j, j ≠ inSlot wf2.program → A4 (b2 wf1.program wf2.program j) = [] := by
    intro j hj
    have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
    rw [hA4, inst_off, hA3_off _ (by vt), hA2_off _ (by vt) (by vt)]
    · exact hA1_off _ (by vt) (by vt) (by vt) (by vt)
    · intro k
      rcases s4_val wf1.program wf2.program k with h | h | h | h | h <;> rw [h] <;> vt
  -- stage 5: the second machine
  obtain ⟨tout5, ht5, h5⟩ := rewound_bank_dock wf2 (b2 wf1.program wf2.program) (b2_inj _ _) A4 r hA4_in hA4_blank
  have h := (((h1.seq h2).seq h3).seq h4).seq h5
  refine ⟨_, _, h, ?_, ?_⟩
  · rw [inst_at _ (b2_inj _ _) _ _ wf2.program.outputTape (b2 wf1.program wf2.program wf2.program.outputTape) rfl, ht5]
  · have hsl : (s r).length ≤ m := by rw [← hts, ← hWl]; exact hWm
    omega

/-- **PA.compose.glue**: the residual `Glue` of the compose plan. -/
noncomputable def glue : Compose.Glue := fun {Req} w s o b4 b5 B wf1 wf2 hB =>
  { program := gprogram wf1.program wf2.program
    realizes := fun r => by
      obtain ⟨F, A5, hstep, hout, hF⟩ := glue_run wf1 wf2 r
      have hB' := hB r
      unfold Compose.glueK at hB'
      obtain ⟨rec, hrun, _, ht, _⟩ := hstep.enlarge (show F ≤ B r by omega)
      exact ⟨rec, hrun, by rw [ht]; exact hout⟩ }

end NearCubicWires.WireExponent3_5.PrimAsm.ComposeGlue
