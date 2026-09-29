import Proof.Wire_3_5.Primitive.SeedFix.C4KWc

/-! # C4KW, part 4: a streams-only word program as a writer stage

A stage (`KWPart oS iS`) is a word program (`WM ns nr`): its outputs are streams `0 … no − 1`, its inputs streams
`no … no + ni − 1`, the rest scratch streams and registers. Compiled and under base's masked reset it runs on
`ns + 2 + nr + 1` tapes; `psl` re-lays them as the stage's (outputs, inputs, then the cell, the scratch streams, the
registers and the log).

* **`wm_blankR`**: base's masked run from blank non-stream tapes, every non-stream tape left as falses (the registers
  back at `0`);
* `psl`, `psl_inj`, `pinv`, `psl_pinv`, `partIn_val`;
* **`part_run`**: a word program's run from the stage's inputs, its outputs framed kept words, its scratch streams
  falses, gives `KWPart.run`'s conclusion at cost `2n + 2`.

Paper quantity of the main type: the kept words writer's stages (P3:2253-2290), as machines. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

theorem pad_falses (c : ℕ) (t : List Bool) (m : ℕ) (h : ZeroPadding.pad c t = List.replicate m false) :
    t = List.replicate t.length false ∧ t.length ≤ m := by
  have hl := congrArg List.length h
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate] at hl
  refine ⟨List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩, by omega⟩
  have : b ∈ ZeroPadding.pad c t := by unfold ZeroPadding.pad; exact List.mem_append_left _ hb
  rw [h] at this
  exact (List.mem_replicate.1 this).2

/-- **A streams-only word program from blank non-stream tapes**: the masked run, the streams the program's, every
other tape (the cell, the log) left as falses. -/
theorem wm_blankR {ns nr : ℕ} (cap : ℕ) (P : WM ns nr) (σ τ : WState ns nr) (n : ℕ) (hw : WExec cap P σ τ n)
    (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hc : σ.cell = false) (hτc : τ.cell = false)
    (hτv : ∀ r, τ.val r = 0) :
    ∃ A' : Fin (ns + 2 + nr + 1) → List Bool,
      Step (MaskedReset.machine P.toProg.compile (fun _ => true)) (2 * n + 2) (fun _ => 0)
        (Fin.addCases (C4Pipe.wblank σ) (fun _ : Fin 1 => [])) (fun _ => 0) A' ∧
      (∀ i, A' (Fin.castAdd 1 (sTape (nr := nr) i)) = τ.st i) ∧
      (∀ j, (∀ i, j ≠ Fin.castAdd 1 (sTape (nr := nr) i)) → ∃ m ≤ n + cap + 1, A' j = List.replicate m false) := by
  have hm := HbM.wm_mask cap n P σ τ n hw (HbM.wenc_H_zero' cap σ hs hv) le_rfl
  have hpad : Fin.addCases (wenc cap σ).A (fun _ : Fin 1 => List.replicate n false) =
      fun i => ZeroPadding.pad (C4Pipe.wcap (ns := ns) (nr := nr) cap n i)
        (Fin.addCases (C4Pipe.wblank σ) (fun _ : Fin 1 => ([] : List Bool)) i) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp only [Fin.addCases_left, C4Pipe.wcap, C4Pipe.wblank, wenc]
      cases hr : role j with
      | stream i => simp
      | cell => simp [hc, ZeroPadding.pad]
      | reg r => simp [hv, FinalPass.Tm.regTape_zero, ZeroPadding.pad]
    · simp [C4Pipe.wcap, ZeroPadding.pad]
  obtain ⟨src, hsrc, hh, ht, hsteps⟩ := hm
  have hcfg : (⟨(MaskedReset.machine P.toProg.compile (fun _ => true)).start, fun _ => 0,
      Fin.addCases (wenc cap σ).A (fun _ : Fin 1 => List.replicate n false)⟩ :
        Configuration (ns + 2 + nr + 1) _) =
      ZeroPadding.config (C4Pipe.wcap (ns := ns) (nr := nr) cap n)
        ⟨(MaskedReset.machine P.toProg.compile (fun _ => true)).start, fun _ => 0,
          Fin.addCases (C4Pipe.wblank σ) (fun _ : Fin 1 => [])⟩ := by
    rw [hpad]; rfl
  rw [hcfg] at hsrc
  obtain ⟨r, hr, hcf, hst, _⟩ := ZeroPadding.run_unpad _ _ _ _ src hsrc
  have hheads : r.final.heads = fun _ => 0 := by
    have := congrArg Configuration.heads hcf
    simp only [ZeroPadding.config] at this
    rw [this, hh]
  have htape : ∀ j, ZeroPadding.pad (C4Pipe.wcap (ns := ns) (nr := nr) cap n j) (r.final.tapes j) =
      Fin.addCases (wenc cap τ).A (fun _ : Fin 1 => List.replicate n false) j := by
    intro j
    have h1 := congrFun (congrArg Configuration.tapes hcf) j
    simp only [ZeroPadding.config] at h1
    rw [h1, ht]
  refine ⟨r.final.tapes, ⟨r, hr, hheads, rfl, by omega⟩, fun i => ?_, fun j hj => ?_⟩
  · have h1 := htape (Fin.castAdd 1 (sTape (nr := nr) i))
    simp only [C4Pipe.wcap, Fin.addCases_left, role_sTape, ZeroPadding.pad_zero] at h1
    rw [h1]
    exact wenc_A_s cap τ i
  · refine Fin.addCases (fun j' => ?_) (fun k => ?_) j hj
    · intro hj'
      have h1 := htape (Fin.castAdd 1 j')
      cases hr' : role j' with
      | stream i => exact absurd (by rw [role_stream hr']) (hj' i)
      | cell =>
        simp only [C4Pipe.wcap, Fin.addCases_left, hr', wenc] at h1
        rw [hτc] at h1
        obtain ⟨e1, e2⟩ := pad_falses 1 _ 1 h1
        exact ⟨_, by omega, e1⟩
      | reg rr =>
        simp only [C4Pipe.wcap, Fin.addCases_left, hr', wenc] at h1
        rw [hτv rr, FinalPass.Tm.regTape_zero] at h1
        obtain ⟨e1, e2⟩ := pad_falses (cap + 1) _ (cap + 1) h1
        exact ⟨_, by omega, e1⟩
    · intro _
      have h1 := htape (Fin.natAdd _ k)
      simp only [C4Pipe.wcap, Fin.addCases_right] at h1
      obtain ⟨e1, e2⟩ := pad_falses n _ n h1
      exact ⟨_, by omega, e1⟩

/-! ## The stage's layout -/

variable {no ni ns nr x : ℕ}

/-- The stage's tape of the compiled program's tape `c`. -/
def psl (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (c : Fin (ns + 2 + nr + 1)) : Fin (no + ni + x) :=
  ⟨if c.val = 0 then 0 else if c.val = 1 then no + ni else if c.val ≤ no + ni then c.val - 1 else c.val, by
    have := c.isLt; split_ifs <;> omega⟩

theorem psl_val (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (c : Fin (ns + 2 + nr + 1)) :
    (psl hle hx c).val = if c.val = 0 then 0 else if c.val = 1 then no + ni else if c.val ≤ no + ni then c.val - 1
      else c.val := rfl

theorem psl_inj (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (h1 : 1 ≤ no + ni) :
    Function.Injective (psl hle hx) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [psl_val hle hx a, psl_val hle hx b] at hv
  have := a.isLt; have := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The compiled tape of a stage tape. -/
def pinv (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (s : Fin (no + ni + x)) : Fin (ns + 2 + nr + 1) :=
  ⟨if s.val = 0 then 0 else if s.val < no + ni then s.val + 1 else if s.val = no + ni then 1 else s.val, by
    have := s.isLt; have := hx; have := hle; split_ifs <;> omega⟩

theorem psl_pinv (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (h1 : 1 ≤ no + ni) (s : Fin (no + ni + x)) :
    psl hle hx (pinv hle hx s) = s := by
  apply Fin.ext
  have hs := s.isLt
  have hp : (pinv hle hx s).val =
      if s.val = 0 then 0 else if s.val < no + ni then s.val + 1 else if s.val = no + ni then 1 else s.val := rfl
  rw [psl_val, hp]
  by_cases a0 : s.val = 0
  · rw [if_pos a0, if_pos rfl, a0]
  · by_cases a1 : s.val < no + ni
    · rw [if_neg a0, if_pos a1, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
    · by_cases a2 : s.val = no + ni
      · rw [if_neg a0, if_neg a1, if_pos a2, if_neg (by omega), if_pos rfl]; omega
      · rw [if_neg a0, if_neg a1, if_neg a2, if_neg a0, if_neg (by omega), if_neg (by omega)]

theorem psl_stream (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (h1 : 1 ≤ no + ni) (i : Fin (ns + 1)) :
    (psl hle hx (Fin.castAdd 1 (sTape (nr := nr) i))).val = if i.val < no + ni then i.val else i.val + 1 := by
  have hc : (Fin.castAdd 1 (sTape (nr := nr) i)).val = if i.val = 0 then 0 else i.val + 1 := rfl
  have := i.isLt
  rw [psl_val, hc]
  by_cases a0 : i.val = 0
  · rw [if_pos a0, if_pos rfl, if_pos (by omega), a0]
  · rw [if_neg a0, if_neg (by omega), if_neg (by omega)]
    by_cases a1 : i.val < no + ni
    · rw [if_pos (by omega), if_pos a1]; omega
    · rw [if_neg (by omega), if_neg a1]

theorem psl_cell (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) :
    (psl hle hx (Fin.castAdd 1 (cTape (ns := ns) (nr := nr)))).val = no + ni := by
  rw [psl_val]; simp [cTape]

theorem psl_log (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) :
    (psl hle hx (Fin.natAdd (ns + 2 + nr) (0 : Fin 1))).val = ns + 2 + nr := by
  rw [psl_val]; simp only [Fin.val_natAdd, Fin.val_zero]; split_ifs <;> omega

theorem partIn_val {no ni : ℕ} (iS : Fin ni → Fin 12) (x : ℕ) (D : HashData) (cap : ℕ) (s : Fin (no + ni + x)) :
    partIn (no := no) iS x D cap s =
      if h : no ≤ s.val ∧ s.val < no + ni then kwIns D cap (iS ⟨s.val - no, by omega⟩) else [] := by
  obtain ⟨v, hv⟩ := s
  by_cases h1 : v < no + ni
  · have e : (⟨v, hv⟩ : Fin (no + ni + x)) = Fin.castAdd x ⟨v, h1⟩ := rfl
    rw [e]; unfold partIn; rw [Fin.addCases_left]
    by_cases h2 : v < no
    · have e2 : (⟨v, h1⟩ : Fin (no + ni)) = Fin.castAdd ni ⟨v, h2⟩ := rfl
      rw [e2, Fin.addCases_left, dif_neg (by simp only [Fin.val_castAdd]; omega)]
    · have e2 : (⟨v, h1⟩ : Fin (no + ni)) = Fin.natAdd no ⟨v - no, by omega⟩ := Fin.ext (by simp; omega)
      rw [e2, Fin.addCases_right, dif_pos (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)]
      congr 2; apply Fin.ext; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
  · have e : (⟨v, hv⟩ : Fin (no + ni + x)) = Fin.natAdd (no + ni) ⟨v - (no + ni), by omega⟩ := Fin.ext (by simp; omega)
    rw [e]; unfold partIn; rw [Fin.addCases_right, dif_neg (by simp only [Fin.val_natAdd]; omega)]

/-- The stage's word program's entry streams: its inputs, every other stream blank. -/
def stIn {no ni ns : ℕ} (iS : Fin ni → Fin 12) (D : HashData) (cap : ℕ) (i : Fin (ns + 1)) : List Bool :=
  if h : no ≤ i.val ∧ i.val < no + ni then kwIns D cap (iS ⟨i.val - no, by omega⟩) else []

/-- The entry word state. -/
def st0' {no ni ns nr : ℕ} (iS : Fin ni → Fin 12) (D : HashData) (cap : ℕ) : WState ns nr :=
  ⟨fun _ => 0, stIn (no := no) iS D cap, fun _ => 0, false⟩

/-- The stage's machine: the compiled program under the masked reset, re-laid by `psl`. -/
noncomputable def partM (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (P : WM ns nr) :=
  RecoveryFocus.machine (psl hle hx) (MaskedReset.machine P.toProg.compile (fun _ => true))

/-- **A streams-only word program as a writer stage**: from the stage's entry, its outputs the framed kept words, its
inputs kept, its scratch left as falses, within `2n + 2` steps. -/
theorem part_run (hle : no + ni ≤ ns + 1) (hx : no + ni + x = ns + 2 + nr + 1) (h1 : 1 ≤ no + ni) (oS : Fin no → Fin 94)
    (iS : Fin ni → Fin 12) (P : WM ns nr) (D : HashData) (cap : ℕ) (wc : ℕ) (τ : WState ns nr) (n : ℕ)
    (hw : WExec wc P (st0' (no := no) iS D cap) τ n) (hτc : τ.cell = false) (hτv : ∀ r, τ.val r = 0) (hwc : wc ≤ n)
    (hout : ∀ j : Fin no, τ.st ⟨j.val, by omega⟩ = frame (kw D cap (oS j)))
    (hinp : ∀ k : Fin ni, τ.st ⟨no + k.val, by omega⟩ = kwIns D cap (iS k))
    (hscr : ∀ i : Fin (ns + 1), no + ni ≤ i.val → ∃ m ≤ n, τ.st i = List.replicate m false) :
    ∃ B : Fin (no + ni + x) → List Bool,
      Step (partM hle hx P) (2 * n + 2) (fun _ => 0) (partIn (no := no) iS x D cap) (fun _ => 0) B ∧
      (∀ j : Fin no, B (Fin.castAdd x (Fin.castAdd ni j)) = frame (kw D cap (oS j))) ∧
      (∀ i : Fin ni, B (Fin.castAdd x (Fin.natAdd no i)) = kwIns D cap (iS i)) ∧
      (∀ k : Fin x, ∃ m ≤ 2 * n + 2, B (Fin.natAdd (no + ni) k) = List.replicate m false) := by
  obtain ⟨A', hA', hs', hn'⟩ := wm_blankR wc P (st0' (no := no) iS D cap) τ n hw (fun _ => rfl) (fun _ => rfl) rfl hτc hτv
  have hentry : ∀ c, partIn (no := no) iS x D cap (psl hle hx c) =
      Fin.addCases (C4Pipe.wblank (st0' (no := no) iS D cap)) (fun _ : Fin 1 => []) c := by
    intro c
    refine Fin.addCases (fun j => ?_) (fun k => ?_) c
    · rw [Fin.addCases_left, partIn_val]
      simp only [C4Pipe.wblank]
      cases hr : role j with
      | stream i =>
        have hj := role_stream hr
        subst hj
        simp only [st0', stIn]
        have hv := psl_stream hle hx h1 i
        by_cases hi : i.val < no + ni
        · rw [if_pos hi] at hv
          by_cases hi2 : no ≤ i.val
          · rw [dif_pos (by rw [hv]; omega), dif_pos (by omega)]
            congr 2; apply Fin.ext; simp only [hv]
          · rw [dif_neg (by rw [hv]; omega), dif_neg (by omega)]
        · rw [if_neg hi] at hv
          rw [dif_neg (by rw [hv]; omega), dif_neg (by omega)]
      | cell =>
        have hj : j = cTape := by
          unfold role at hr; split_ifs at hr with h0 h1 <;> first | exact Fin.ext h1 | cases hr
        subst hj
        rw [dif_neg (by rw [psl_cell]; omega)]
      | reg r =>
        have hj2 : ns + 2 ≤ j.val := by
          unfold role at hr; split_ifs at hr with h0 h1 h2 <;> first | omega | cases hr
        rw [dif_neg (by rw [psl_val]; simp only [Fin.val_castAdd]; split_ifs <;> omega)]
    · rw [Fin.addCases_right, partIn_val]
      have hk : k = 0 := Subsingleton.elim _ _
      subst hk
      rw [dif_neg (by rw [psl_log]; omega)]
  have hd := Block.dockKeep hA' (psl hle hx) (psl_inj hle hx h1) (fun _ => 0) (partIn (no := no) iS x D cap) (fun _ => rfl)
    hentry
  refine ⟨install (psl hle hx) (partIn (no := no) iS x D cap) A', hd, fun j => ?_, fun i => ?_, fun k => ?_⟩
  · have e : Fin.castAdd x (Fin.castAdd ni j) = psl hle hx (Fin.castAdd 1 (sTape (nr := nr) ⟨j.val, by omega⟩)) := by
      apply Fin.ext; rw [psl_stream hle hx h1]; simp only [Fin.val_castAdd]; rw [if_pos (by omega)]
    rw [e, install_slot _ (psl_inj hle hx h1), hs', hout]
  · have e : Fin.castAdd x (Fin.natAdd no i) = psl hle hx (Fin.castAdd 1 (sTape (nr := nr) ⟨no + i.val, by omega⟩)) := by
      apply Fin.ext; rw [psl_stream hle hx h1]; simp only [Fin.val_castAdd, Fin.val_natAdd]; rw [if_pos (by omega)]
    rw [e, install_slot _ (psl_inj hle hx h1), hs', hinp]
  · rw [← psl_pinv hle hx h1 (Fin.natAdd (no + ni) k), install_slot _ (psl_inj hle hx h1)]
    by_cases hstr : ∃ i : Fin (ns + 1), pinv hle hx (Fin.natAdd (no + ni) k) = Fin.castAdd 1 (sTape (nr := nr) i)
    · obtain ⟨i, hi⟩ := hstr
      rw [hi, hs']
      have hv := congrArg Fin.val (congrArg (psl hle hx) hi)
      rw [psl_pinv hle hx h1, psl_stream hle hx h1] at hv
      simp only [Fin.val_natAdd] at hv
      have hi2 : no + ni ≤ i.val := by split_ifs at hv <;> omega
      obtain ⟨m, hm, e⟩ := hscr i hi2
      exact ⟨m, by omega, e⟩
    · push Not at hstr
      obtain ⟨m, hm, e⟩ := hn' _ hstr
      exact ⟨m, by omega, e⟩

end NearCubicWires.WireExponent3_5.PrimT.C4KW
