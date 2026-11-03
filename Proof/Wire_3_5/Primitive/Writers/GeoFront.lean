import Proof.Wire_3_5.Primitive.Writers.DockW
import Proof.Wire_3_5.Primitive.Writers.StarNums
import Proof.Wire_3_5.Primitive.Writers.Emit
import Proof.Wire_3_5.UnionMachine.FrontFill
import Proof.Wire_3_5.Lists.ListMachineRowLoad
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase
import Proof.Rows.CapReader

/-! # PA (d): a register-language writer on the request word (the geometry writers' common front)

The pool-geometry fields (`PrimT.C4Geo`) are functions of the call's star parameters (P3:1188-1216) and of the
request's translation, both read from the request word (P3:3119-3120: "The algorithm receives polynomial-bit integer
circuit descriptions"). Each geometry writer is one program of C5's register language `WM GS GR` run from the
request; this module builds the common machine around it, ONCE:

1. C2's `Unframe` under `maskBlank`: the raw request `w = natWord n ++ sfx`;
2. base `CapReader.natural_run` under `maskBlank`: `1^n` on the program's stream `gNT` and on the fill run's input;
3. base `UnaryCalc.poly_step Dv Cv`: the fill count `1^W`, `W = Cv(n+1)^Dv`, on stream `gCT`;
4. the fill (C6's `FrontFill.fillP`): the registers at capacity `2W + 2`;
5. the program;
6. a masked reset: every head back at `0`.

**`geo_run`**: for any program whose run from `σG w n W` leaves the request on `gIN` and the word `v` on `gOUT`, the
machine is a `WriterIfaceJ.WriterRun` from `frame w` to `v`; `geoStage` is its `WriterStage`.

Paper quantity of the main type: the field `v` written on the writer's output port (for: `C4Geo.sideField P`,
`1^(C4Geo.width P)`, `C4Geo.colsField P`, …). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## The layout -/

/-- The program's streams: request, `1^n`, fill count, fill marker, output, and scratch `5 … 12`. -/
abbrev GS : ℕ := 12
/-- The program's registers. -/
abbrev GR : ℕ := 64
/-- The program's tapes. -/
abbrev WT : ℕ := GS + 2 + GR
/-- The front's tapes: the raw request, a log, CapReader (with its reset log), the fill run. -/
abbrev GX (Dv : ℕ) : ℕ := 14 + UnaryCalc.tapes Dv
/-- The layout. -/
abbrev GLt (Dv : ℕ) : ℕ := WT + GX Dv

def gIN : Fin (GS + 1) := 0
def gNT : Fin (GS + 1) := 1
def gCT : Fin (GS + 1) := 2
def gAUX : Fin (GS + 1) := 3
def gOUT : Fin (GS + 1) := 4

section Tapes
variable {Dv : ℕ}

def wt (j : Fin WT) : Fin (GLt Dv) := Fin.castAdd _ j
def xt (k : Fin (GX Dv)) : Fin (GLt Dv) := Fin.natAdd WT k
def raw : Fin (GLt Dv) := xt (Fin.castAdd (UnaryCalc.tapes Dv) (0 : Fin 14))
def lg : Fin (GLt Dv) := xt (Fin.castAdd (UnaryCalc.tapes Dv) (1 : Fin 14))
def cp (k : Fin 12) : Fin (GLt Dv) := xt (Fin.castAdd (UnaryCalc.tapes Dv) (Fin.natAdd 2 k))
def pw (k : Fin (UnaryCalc.tapes Dv)) : Fin (GLt Dv) := xt (Fin.natAdd 14 k)
def ws (s : Fin (GS + 1)) : Fin (GLt Dv) := wt (sTape (nr := GR) s)

theorem raw_val : (raw (Dv := Dv)).val = WT := rfl
theorem lg_val : (lg (Dv := Dv)).val = WT + 1 := rfl
theorem cp_val (k : Fin 12) : (cp (Dv := Dv) k).val = WT + (2 + k.val) := rfl
theorem pw_val (k : Fin (UnaryCalc.tapes Dv)) : (pw (Dv := Dv) k).val = WT + (14 + k.val) := rfl
theorem ws_val (s : Fin (GS + 1)) : (ws (Dv := Dv) s).val = if s.val = 0 then 0 else s.val + 1 := rfl
theorem ws_lt (s : Fin (GS + 1)) : (ws (Dv := Dv) s).val < WT := by
  have h1 : WT = 78 := rfl
  have h2 : GS = 12 := rfl
  have hs : s.val < 13 := s.isLt
  rw [ws_val, h1]; split <;> omega

theorem ws_inj : Function.Injective (ws (Dv := Dv)) := fun _ _ h => sTape_inj (Fin.castAdd_injective _ _ h)

/-- A docked run with every head at `0`, into an ambient bank whose heads on the slots are `0`. -/
theorem dockZ {t u s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A H (install slots A tout) := by
  have d := Rec.dockRun h slots hi H A hH hA
  refine d.congr ?_ rfl
  funext i
  by_cases hs : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := hs
    rw [dockH_slot _ hi, hH j]
  · exact dockH_other _ _ _ _ (fun j e => hs ⟨j, e⟩)
theorem pw_inj : Function.Injective (pw (Dv := Dv)) := by
  intro a b h; have := congrArg Fin.val h; rw [pw_val, pw_val] at this; exact Fin.ext (by omega)

end Tapes

/-! ## Stage 1: the raw request -/

section Stages
variable {Dv : ℕ}

/-- The writer's entry bank. -/
def A0 (w : List Bool) : Fin (GLt Dv) → List Bool := fun i => if i = ws gIN then frame w else []

def slots1 : Fin 3 → Fin (GLt Dv) := ![ws gIN, raw, lg]

theorem slots1_inj : Function.Injective (slots1 (Dv := Dv)) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [slots1, ws_val, raw_val, lg_val, gIN] at hv ⊢

noncomputable def F1 (Dv : ℕ) := RecoveryFocus.machine (slots1 (Dv := Dv)) (MaskedReset.machine Unframe.machine (fun _ => true))

theorem f1_step (w : List Bool) : ∃ B1 : Fin (GLt Dv) → List Bool,
    Step (F1 Dv) (2 * (2 * w.length + 1) + 2) (fun _ => 0) (A0 w) (fun _ => 0) B1 ∧
    B1 (ws gIN) = frame w ∧ B1 raw = w ∧ (∀ i, i ≠ ws gIN → i ≠ raw → i ≠ lg → B1 i = A0 w i) := by
  obtain ⟨m1, h⟩ := maskBlank (Unframe.run [] w [] [] []) (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have hr : (raw (Dv := Dv)) ≠ ws gIN := fun e => by have := congrArg Fin.val e; rw [raw_val, ws_val] at this; simp [gIN] at this
  have hl : (lg (Dv := Dv)) ≠ ws gIN := fun e => by have := congrArg Fin.val e; rw [lg_val, ws_val] at this; simp [gIN] at this
  have d := Rec.dockRun h (slots1 (Dv := Dv)) slots1_inj (fun _ => 0) (A0 w) (by intro j; fin_cases j <;> rfl)
    (by
      intro j
      fin_cases j
      · change A0 w (ws gIN) = [] ++ frame w ++ []
        simp [A0]
      · change A0 w raw = overlay [] []
        simp [A0, hr, overlay_nil]
      · change A0 w lg = List.replicate 0 false
        simp [A0, hl])
  have eH : ∀ H' : Fin 3 → ℕ, (∀ j, H' j = 0) → dockH (slots1 (Dv := Dv)) (fun _ => 0) H' = fun _ => 0 := by
    intro H' hH'
    funext i
    by_cases hs : ∃ j, slots1 (Dv := Dv) j = i
    · obtain ⟨j, rfl⟩ := hs
      rw [dockH_slot _ slots1_inj, hH']
    · exact dockH_other _ _ _ _ (fun j e => hs ⟨j, e⟩)
  refine ⟨_, d.congr (eH _ (by intro j; fin_cases j <;> rfl)) rfl, ?_, ?_, ?_⟩
  · change install slots1 (A0 w) _ (slots1 0) = _
    rw [install_slot _ slots1_inj]
    simp
    rfl
  · change install slots1 (A0 w) _ (slots1 1) = _
    rw [install_slot _ slots1_inj]
    simp [overlay_nil]
    rfl
  · intro i h1 h2 h3
    refine install_other _ _ _ _ (fun j => ?_)
    fin_cases j
    · exact fun e => h1 e.symm
    · exact fun e => h2 e.symm
    · exact fun e => h3 e.symm

/-! ## Stage 2: `1^n` by base `CapReader` -/

def slots2 (j : Fin 12) : Fin (GLt Dv) :=
  if j = 0 then raw else if j = 8 then ws gNT else if j = 9 then pw (UnaryCalc.inputTape Dv) else cp j

theorem slots2_val (j : Fin 12) : (slots2 (Dv := Dv) j).val =
    if j = 0 then WT else if j = 8 then 2 else if j = 9 then WT + 14 else WT + (2 + j.val) := by
  unfold slots2
  split_ifs <;> rfl

theorem slots2_inj : Function.Injective (slots2 (Dv := Dv)) := by
  have hWT : WT = 78 := rfl
  intro a b h
  have hv := congrArg Fin.val h
  rw [slots2_val, slots2_val, hWT] at hv
  fin_cases a <;> fin_cases b <;> simp at hv ⊢

noncomputable def F2 (Dv : ℕ) :=
  RecoveryFocus.machine (slots2 (Dv := Dv)) (MaskedReset.machine PCJ45bee56da9f34d5a_CapReader.machine (fun _ => true))

theorem f2_step (n : ℕ) (w sfx : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx) (B1 : Fin (GLt Dv) → List Bool)
    (hraw : B1 raw = w) (hNT : B1 (ws gNT) = []) (hpw : B1 (pw (UnaryCalc.inputTape Dv)) = [])
    (hcp : ∀ k, B1 (cp k) = []) :
    ∃ B2 : Fin (GLt Dv) → List Bool,
      Step (F2 Dv) (2 * (8 * n + 20 * natBitLength n + 17) + 2) (fun _ => 0) B1 (fun _ => 0) B2 ∧
      B2 (ws gNT) = List.replicate n true ∧ B2 (pw (UnaryCalc.inputTape Dv)) = List.replicate n true ∧
      (∀ i, (∀ j, slots2 j ≠ i) → B2 i = B1 i) := by
  obtain ⟨H, A, h, hout⟩ := PCJ45bee56da9f34d5a_CapReader.natural_run [] sfx n
  obtain ⟨_, _, h8, _, h9, _, _, _⟩ := hout
  obtain ⟨m2, hm⟩ := maskBlank h (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have eh0 : (Fin.addCases (PCJ45bee56da9f34d5a_CapReader.initialHeads ([] : List Bool).length) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · fin_cases a <;> rfl
    · simp
  have eh1 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else H i) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hm' := (hm.congr_in eh0 rfl).congr eh1 rfl
  have d := dockZ hm' (slots2 (Dv := Dv)) slots2_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j
    fin_cases j
    · show B1 raw = _
      rw [hraw, hw]; rfl
    · show B1 (cp 1) = _; rw [hcp]; rfl
    · show B1 (cp 2) = _; rw [hcp]; rfl
    · show B1 (cp 3) = _; rw [hcp]; rfl
    · show B1 (cp 4) = _; rw [hcp]; rfl
    · show B1 (cp 5) = _; rw [hcp]; rfl
    · show B1 (cp 6) = _; rw [hcp]; rfl
    · show B1 (cp 7) = _; rw [hcp]; rfl
    · show B1 (ws gNT) = _; rw [hNT]; rfl
    · show B1 (pw (UnaryCalc.inputTape Dv)) = _; rw [hpw]; rfl
    · show B1 (cp 10) = _; rw [hcp]; rfl
    · show B1 (cp 11) = _; rw [hcp]; rfl)
  refine ⟨_, d, ?_, ?_, fun i hi => install_other _ _ _ _ hi⟩
  · have e := install_slot (slots2 (Dv := Dv)) slots2_inj B1 (Fin.addCases (motive := fun _ => List Bool) A (fun _ : Fin 1 => List.replicate m2 false)) 8
    have e8 : slots2 (Dv := Dv) 8 = ws gNT := by unfold slots2; rfl
    rw [e8] at e
    rw [e]
    exact h8
  · have e := install_slot (slots2 (Dv := Dv)) slots2_inj B1 (Fin.addCases (motive := fun _ => List Bool) A (fun _ : Fin 1 => List.replicate m2 false)) 9
    have e9 : slots2 (Dv := Dv) 9 = pw (UnaryCalc.inputTape Dv) := by unfold slots2; rfl
    rw [e9] at e
    rw [e]
    exact h9

/-! ## Stage 3: the fill count `1^W` -/

def slots3 (k : Fin (UnaryCalc.tapes Dv)) : Fin (GLt Dv) :=
  if k = UnaryCalc.outputTape Dv then ws gCT else pw k

theorem slots3_inj : Function.Injective (slots3 (Dv := Dv)) := by
  have hWT : WT = 78 := rfl
  have hct : (ws (Dv := Dv) gCT).val = 3 := rfl
  intro a b h
  unfold slots3 at h
  split_ifs at h with ha hb hb
  · rw [ha, hb]
  · exfalso; have hv := congrArg Fin.val h; rw [hct, pw_val, hWT] at hv; omega
  · exfalso; have hv := congrArg Fin.val h; rw [hct, pw_val, hWT] at hv; omega
  · exact pw_inj h

noncomputable def F3 (Dv Cv : ℕ) := RecoveryFocus.machine (slots3 (Dv := Dv)) (PCPSerializerCapacity.Power.machine Dv Cv)

theorem f3_step (Cv n : ℕ) (B2 : Fin (GLt Dv) → List Bool) (hin : B2 (pw (UnaryCalc.inputTape Dv)) = List.replicate n true)
    (hct : B2 (ws gCT) = []) (hpw : ∀ k, k ≠ UnaryCalc.inputTape Dv → B2 (pw k) = []) :
    ∃ B3 : Fin (GLt Dv) → List Bool,
      Step (F3 Dv Cv) (PCPSerializerCapacity.Power.budget Dv Cv n) (fun _ => 0) B2 (fun _ => 0) B3 ∧
      B3 (ws gCT) = List.replicate (UnaryCalc.value Dv Cv n) true ∧ (∀ i, (∀ j, slots3 j ≠ i) → B3 i = B2 i) := by
  obtain ⟨out, h, -, ho⟩ := UnaryCalc.poly_step Dv Cv n
  have hio : UnaryCalc.outputTape Dv ≠ UnaryCalc.inputTape Dv := by
    intro e
    have := congrArg Fin.val e
    rw [show (UnaryCalc.outputTape Dv).val = 3 + 2 * Dv from rfl, show (UnaryCalc.inputTape Dv).val = 0 from rfl] at this
    omega
  have d := dockZ h (slots3 (Dv := Dv)) slots3_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro k
    unfold slots3
    split_ifs with hk
    · subst hk
      rw [hct]
      have hv : (UnaryCalc.outputTape Dv).val ≠ 0 := fun e => hio (Fin.ext (by rw [e]; rfl))
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hv]
    · by_cases hi : k = UnaryCalc.inputTape Dv
      · subst hi
        rw [hin]
        simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
      · rw [hpw k hi]
        have hv : k.val ≠ 0 := fun e => hi (Fin.ext e)
        simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hv])
  refine ⟨_, d, ?_, fun i hi => install_other _ _ _ _ hi⟩
  have e := install_slot (slots3 (Dv := Dv)) slots3_inj B2 out (UnaryCalc.outputTape Dv)
  rw [show slots3 (Dv := Dv) (UnaryCalc.outputTape Dv) = ws gCT from by unfold slots3; rw [if_pos rfl]] at e
  rw [e]
  exact ho

end Stages

/-! ## Stage 4: the fill -/

/-- The register tapes (the fill's targets). -/
def regSelG (j : Fin WT) : Bool := decide (GS + 2 ≤ j.val)

/-- The program's layout before the fill: the request, `1^n`, `1^W`. -/
def rawG (w : List Bool) (n W : ℕ) : Fin WT → List Bool := fun j =>
  if j = sTape gIN then RepairOrdinary.frame w else if j = sTape gNT then List.replicate n true
  else if j = sTape gCT then List.replicate W true else []

/-- **The program's start state**: registers `0` at capacity `2W + 2`, the request, `1^n`, `1^W` and the fill's marker
tape on their streams, every head at `0`. -/
def σG (w : List Bool) (n W : ℕ) : WState GS GR :=
  ⟨fun _ => 0, fun s => if s = gIN then RepairOrdinary.frame w else if s = gNT then List.replicate n true
    else if s = gCT then List.replicate W true else if s = gAUX then List.replicate (2 * W + 3) false else [],
    fun _ => 0, false⟩

def fillG : Prog WT :=
  .seq (UnionMachine.FrontFill.fillP (sTape gCT) (sTape gAUX) regSelG) (.act (writeAt cTape false) (fun _ => .stay))

theorem sTape_valG (s : Fin (GS + 1)) : (sTape (nr := GR) s).val = if s.val = 0 then 0 else s.val + 1 := rfl

theorem sTape_eq_iffG (a b : Fin (GS + 1)) : sTape (nr := GR) a = sTape b ↔ a = b :=
  ⟨fun h => sTape_inj h, fun h => h ▸ rfl⟩

theorem regSelG_s (s : Fin (GS + 1)) : regSelG (sTape (nr := GR) s) = false := by
  have : s.val < 13 := s.isLt
  simp only [regSelG, sTape_valG, decide_eq_false_iff_not, not_le]
  show _ < 12 + 2
  split <;> omega

theorem regSelG_c : regSelG (cTape (ns := GS) (nr := GR)) = false := by
  unfold regSelG
  rw [show (cTape (ns := GS) (nr := GR)).val = 1 from rfl]
  decide

theorem regSelG_r (r : Fin GR) : regSelG (rTape (ns := GS) r) = true := by simp [regSelG, rTape]

theorem rawG_c (w : List Bool) (n W : ℕ) : rawG w n W cTape = [] := by
  simp [rawG, fun s => (sTape_ne_c (nr := GR) (ns := GS) s).symm]

theorem rawG_r (w : List Bool) (n W : ℕ) (r : Fin GR) : rawG w n W (rTape r) = [] := by
  simp [rawG, fun s => (sTape_ne_r (nr := GR) (ns := GS) s r).symm]

theorem rawG_s (w : List Bool) (n W : ℕ) (s : Fin (GS + 1)) : rawG w n W (sTape s) =
    if s = gIN then RepairOrdinary.frame w else if s = gNT then List.replicate n true
    else if s = gCT then List.replicate W true else [] := by
  simp only [rawG, sTape_eq_iffG]

theorem fillG_exec (w : List Bool) (n W : ℕ) :
    Exec fillG ⟨fun _ => 0, rawG w n W⟩ (wenc (2 * W + 2) (σG w n W)) (11 * W + 20 + 1 + 1) := by
  have hca : sTape (nr := GR) gCT ≠ sTape gAUX := fun h => absurd (sTape_inj h) (by decide)
  have hA : ∀ i, UnionMachine.FrontFill.side (sTape (nr := GR) gAUX) regSelG i → rawG w n W i = [] := by
    intro i hi
    rcases hi with hi | hi
    · rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [regSelG_s] at hi; exact absurd hi (by decide)
      · rw [regSelG_c] at hi; exact absurd hi (by decide)
      · exact rawG_r w n W r
    · subst hi
      rw [rawG_s]
      simp [gIN, gNT, gCT, gAUX]
  have e1 := UnionMachine.FrontFill.fillP_exec (sTape gCT) (sTape gAUX) regSelG (fun _ => 0) (rawG w n W) hca
    (regSelG_s _) (regSelG_s _) W (by rw [rawG_s]; simp [gIN, gNT, gCT]) (fun _ _ => rfl) hA
  have e2 := Exec.act (UnionMachine.FrontFill.stB (sTape gCT) (sTape gAUX) regSelG (fun _ => 0) (rawG w n W) W 0)
    (writeAt (cTape (ns := GS) (nr := GR)) false) (fun _ => .stay)
  have eB : (UnionMachine.FrontFill.stB (sTape gCT) (sTape gAUX) regSelG (fun _ => 0) (rawG w n W) W 0).act
      (writeAt (cTape (ns := GS) (nr := GR)) false) (fun _ => .stay) = wenc (2 * W + 2) (σG w n W) := by
    apply Bank.ext'
    · intro j
      simp only [Bank.act, HeadMove.apply, UnionMachine.FrontFill.stB]
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_H_s]
        split_ifs <;> simp [σG] <;> omega
      · rw [wenc_H_c]
        split_ifs <;> omega
      · rw [wenc_H_r]
        split_ifs <;> simp [σG] <;> omega
    · intro j
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [wenc_A_s]
        simp only [Bank.act, writeAt, sTape_ne_c, if_false, UnionMachine.FrontFill.stB, regSelG_s, Bool.false_eq_true,
          sTape_eq_iffG, rawG_s, σG]
        by_cases hx : s = gAUX
        · subst hx; simp [gIN, gNT, gCT, gAUX]
        · simp [hx]
      · rw [wenc_A_c]
        simp only [Bank.act, writeAt, if_true, UnionMachine.FrontFill.stB, regSelG_c, Bool.false_eq_true, if_false,
          fun s => (sTape_ne_c (nr := GR) (ns := GS) s).symm, rawG_c]
        simp [σG, UnionMachine.FrontFill.side, regSelG_c, fun s => (sTape_ne_c (nr := GR) (ns := GS) s).symm]
        rfl
      · rw [wenc_A_r]
        simp only [Bank.act, writeAt, cTape_ne_r, (cTape_ne_r _).symm, if_false, UnionMachine.FrontFill.stB,
          regSelG_r, if_true, σG]
        rw [regTape_zero]
  rw [← eB]
  exact Exec.seq e1 e2

/-! ## The machine and its run -/

/-- The writer before its teardown: the front and the program. -/
noncomputable def geoInner (prog : WM GS GR) (Dv Cv : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (F1 Dv) (F2 Dv)) (F3 Dv Cv))
    (TapeEmbedding.machine (GX Dv) fillG.compile)) (TapeEmbedding.machine (GX Dv) prog.toProg.compile)

/-- **A register-language writer on the request word** (every head back at `0`). -/
noncomputable def geoM (prog : WM GS GR) (Dv Cv : ℕ) := MaskedReset.machine (geoInner prog Dv Cv) (fun _ => true)

/-- The request port. -/
def gInP (Dv : ℕ) : Fin (GLt Dv + 1) := Fin.castAdd 1 (ws gIN)

/-- The output port. -/
def gOutP (Dv : ℕ) : Fin (GLt Dv + 1) := Fin.castAdd 1 (ws gOUT)

theorem gInP_ne_out (Dv : ℕ) : gInP Dv ≠ gOutP Dv := by
  intro h
  have := congrArg Fin.val h
  simp only [gInP, gOutP, Fin.val_castAdd, ws_val] at this
  simp [gIN, gOUT] at this

/-- The front's cost before the program. -/
def frontCost (w : List Bool) (n Dv Cv : ℕ) : ℕ :=
  2 * (2 * w.length + 1) + 2 + 1 + (2 * (8 * n + 20 * natBitLength n + 17) + 2) + 1 +
    PCPSerializerCapacity.Power.budget Dv Cv n + 1 + (11 * UnaryCalc.value Dv Cv n + 20 + 1 + 1) + 1

section Hlp
variable {Dv : ℕ}

theorem ws_IN : (ws (Dv := Dv) gIN).val = 0 := rfl
theorem ws_NT : (ws (Dv := Dv) gNT).val = 2 := rfl
theorem ws_CT : (ws (Dv := Dv) gCT).val = 3 := rfl

theorem slots2_ne (i : Fin (GLt Dv)) (h0 : i.val ≠ WT) (h2 : i.val ≠ 2) (h14 : i.val ≠ WT + 14)
    (hr : i.val < WT + 3 ∨ WT + 14 ≤ i.val) : ∀ j, slots2 (Dv := Dv) j ≠ i := by
  intro j e
  have hv := congrArg Fin.val e
  have hj := j.isLt
  rw [slots2_val] at hv
  split_ifs at hv <;> omega

theorem slots3_ne (i : Fin (GLt Dv)) (h3 : i.val ≠ 3) (hr : i.val < WT + 14) : ∀ j, slots3 (Dv := Dv) j ≠ i := by
  intro j e
  have hv := congrArg Fin.val e
  unfold slots3 at hv
  split_ifs at hv
  · rw [ws_CT] at hv; omega
  · rw [pw_val] at hv; omega

theorem slots1_ne (i : Fin (GLt Dv)) (h0 : i.val ≠ 0) (h1 : i.val ≠ WT) (h2 : i.val ≠ WT + 1) :
    i ≠ ws gIN ∧ i ≠ raw ∧ i ≠ lg :=
  ⟨fun e => h0 (by rw [e]; rfl), fun e => h1 (by rw [e]; rfl), fun e => h2 (by rw [e]; rfl)⟩

end Hlp

/-- **The writer's run** (`WriterIfaceJ.WriterRun`): for any program whose run from `σG w n W` (`W = Cv(n+1)^Dv`,
registers at capacity `2W + 2`) leaves the request on `gIN` and `v` on `gOUT` within `c` steps, the machine writes
`v` from `frame w` (`w = natWord n ++ sfx`) within the budget. -/
theorem geo_run (prog : WM GS GR) (Dv Cv n c Bud : ℕ) (w sfx v : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx)
    (σF : WState GS GR)
    (hx : WExec (2 * UnaryCalc.value Dv Cv n + 2) prog (σG w n (UnaryCalc.value Dv Cv n)) σF c)
    (hIN : σF.st gIN = RepairOrdinary.frame w) (hOUT : σF.st gOUT = v)
    (hB : 2 * (frontCost w n Dv Cv + c) + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (geoM prog Dv Cv) Bud (gInP Dv) (gOutP Dv) w v := by
  set W := UnaryCalc.value Dv Cv n with hW
  have hWT : WT = 78 := rfl
  -- 1
  obtain ⟨B1, s1, b1in, b1raw, b1o⟩ := f1_step (Dv := Dv) w
  have hA0 : ∀ i : Fin (GLt Dv), i ≠ ws gIN → A0 w i = [] := fun i hi => by simp [A0, hi]
  have k1 : ∀ i : Fin (GLt Dv), i.val ≠ 0 → i.val ≠ WT → i.val ≠ WT + 1 → B1 i = [] := by
    intro i h0 h1 h2
    obtain ⟨n0, n1, n2⟩ := slots1_ne i h0 h1 h2
    rw [b1o i n0 n1 n2, hA0 i n0]
  -- 2
  obtain ⟨B2, s2, b2nt, b2pw, b2o⟩ := f2_step (Dv := Dv) n w sfx hw B1 b1raw
    (k1 _ (by rw [ws_NT]; omega) (by rw [ws_NT]; omega) (by rw [ws_NT]; omega))
    (k1 _ (by rw [pw_val]; omega) (by rw [pw_val]; omega) (by rw [pw_val]; omega))
    (fun k => k1 _ (by rw [cp_val]; omega) (by rw [cp_val]; omega) (by rw [cp_val]; omega))
  have k2 : ∀ i : Fin (GLt Dv), i.val ≠ 0 → i.val ≠ 2 → i.val ≠ WT → i.val ≠ WT + 1 → i.val ≠ WT + 14 →
      (i.val < WT + 3 ∨ WT + 14 ≤ i.val) → B2 i = [] := by
    intro i h0 h2 h1 h11 h14 hr
    rw [b2o i (slots2_ne i h1 h2 h14 hr)]
    exact k1 i h0 h1 h11
  -- 3
  obtain ⟨B3, s3, b3ct, b3o⟩ := f3_step (Dv := Dv) Cv n B2 b2pw
    (k2 _ (by rw [ws_CT]; omega) (by rw [ws_CT]; omega) (by rw [ws_CT]; omega) (by rw [ws_CT]; omega)
      (by rw [ws_CT]; omega) (by rw [ws_CT]; omega))
    (fun k hk => by
      have hk0 : k.val ≠ 0 := fun e => hk (Fin.ext e)
      exact k2 _ (by rw [pw_val]; omega) (by rw [pw_val]; omega) (by rw [pw_val]; omega) (by rw [pw_val]; omega)
        (by rw [pw_val]; omega) (by rw [pw_val]; omega))
  have k3 : ∀ i : Fin (GLt Dv), i.val ≠ 0 → i.val ≠ 2 → i.val ≠ 3 → i.val < WT → B3 i = [] := by
    intro i h0 h2 h3 hi
    rw [b3o i (slots3_ne i h3 (by omega))]
    exact k2 i h0 h2 (by omega) (by omega) (by omega) (Or.inl (by omega))
  -- the program's part of the bank
  have hB3 : (Fin.addCases (rawG w n W) (fun k => B3 (xt k)) : Fin (GLt Dv) → List Bool) = B3 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp only [Fin.addCases_left]
      show rawG w n W j = B3 (wt j)
      rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [rawG_s]
        by_cases s1 : s = gIN
        · subst s1
          rw [if_pos rfl]
          show _ = B3 (ws gIN)
          rw [b3o _ (slots3_ne _ (by rw [ws_IN]; omega) (by rw [ws_IN]; omega)),
            b2o _ (slots2_ne _ (by rw [ws_IN]; omega) (by rw [ws_IN]; omega) (by rw [ws_IN]; omega)
              (Or.inl (by rw [ws_IN]; omega)))]
          exact b1in.symm
        · by_cases s2 : s = gNT
          · subst s2
            rw [if_neg (by decide), if_pos rfl]
            show _ = B3 (ws gNT)
            rw [b3o _ (slots3_ne _ (by rw [ws_NT]; omega) (by rw [ws_NT]; omega))]
            exact b2nt.symm
          · by_cases s3 : s = gCT
            · subst s3
              rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
              exact b3ct.symm
            · rw [if_neg s1, if_neg s2, if_neg s3]
              have hsv := ws_lt (Dv := Dv) s
              have v0 : (ws (Dv := Dv) s).val ≠ 0 := fun e => s1 (ws_inj (Fin.ext (by rw [e]; rfl)))
              have v2 : (ws (Dv := Dv) s).val ≠ 2 := fun e => s2 (ws_inj (Fin.ext (by rw [e]; rfl)))
              have v3 : (ws (Dv := Dv) s).val ≠ 3 := fun e => s3 (ws_inj (Fin.ext (by rw [e]; rfl)))
              exact (k3 (ws s) v0 v2 v3 hsv).symm
      · have hv : (wt (Dv := Dv) (cTape (ns := GS) (nr := GR))).val = 1 := rfl
        rw [rawG_c]
        exact (k3 _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)).symm
      · have hv : (wt (Dv := Dv) (rTape (ns := GS) r)).val = GS + 2 + r.val := rfl
        have hGS : GS = 12 := rfl
        have hr := r.isLt
        have hGR : GR = 64 := rfl
        rw [rawG_r]
        exact (k3 _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)).symm
    · simp only [Fin.addCases_right]
      rfl
  -- 4, 5
  have s4 := (Exec.step (fillG_exec w n W)).embed (fun _ : Fin (GX Dv) => 0) (fun k => B3 (xt k))
  have eH0 : (Fin.addCases (fun _ => 0) (fun _ : Fin (GX Dv) => 0) : Fin (GLt Dv) → ℕ) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have s4' := s4.congr_in eH0 hB3
  have s5 := (WExec.exec (2 * W + 2) hx).step.embed (fun _ : Fin (GX Dv) => 0) (fun k => B3 (xt k))
  have si := (((s1.seq s2).seq s3).seq s4').seq s5
  obtain ⟨m, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (GLt Dv + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have e2 : (Fin.addCases (A0 w) (fun _ : Fin 1 => List.replicate 0 false) : Fin (GLt Dv + 1) → List Bool) =
      WriterIface.inBank (gInP Dv) w := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · by_cases ha : a = ws gIN
      · subst ha
        simp [A0, WriterIface.inBank, gInP]
      · have hne : Fin.castAdd 1 a ≠ gInP Dv := fun e => ha (Fin.castAdd_injective _ _ e)
        simp [A0, WriterIface.inBank, ha, hne]
    · have hne : Fin.natAdd (GLt Dv) u ≠ gInP Dv := by
        intro e
        have := congrArg Fin.val e
        simp only [Fin.val_natAdd, gInP, Fin.val_castAdd] at this
        have := (ws (Dv := Dv) gIN).isLt
        omega
      simp [WriterIface.inBank, hne]
  have e3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else
      (Fin.addCases (wenc (2 * W + 2) σF).H (fun _ : Fin (GX Dv) => 0) : Fin (GLt Dv) → ℕ) i) (fun _ : Fin 1 => 0) :
      Fin (GLt Dv + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  set Tf : Fin (GLt Dv + 1) → List Bool := Fin.addCases
    (Fin.addCases (wenc (2 * W + 2) σF).A (fun k : Fin (GX Dv) => B3 (xt k)))
    (fun _ : Fin 1 => List.replicate m false) with hTf
  have hstep : Step (geoM prog Dv Cv) Bud (fun _ => 0) (WriterIface.inBank (gInP Dv) w) (fun _ => 0) Tf :=
    ((sm.congr_in e1 e2).congr e3 rfl).enlarge (by unfold frontCost at hB; omega)
  refine ⟨fun j => if j = gInP Dv ∨ j = gOutP Dv then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : j = gInP Dv ∨ j = gOutP Dv
    · simp [hj]
    · have hin : j ≠ gInP Dv := fun e => hj (Or.inl e)
      have hlen : ∀ (t s n' : ℕ) (p : Machine t s) (hi ho : Fin t → ℕ) (ti tf : Fin t → List Bool),
          Step p n' hi ti ho tf → ∀ i k, hi i ≤ k → (ti i).length ≤ k → (tf i).length ≤ k + n' := by
        intro t s n' p hi ho ti tf h i k hh ht
        obtain ⟨r, hr, _, hT, _⟩ := h
        have := DecompositionSource.one_tape_support p n' ⟨p.start, hi, ti⟩ r i k hr hh ht
        rw [hT] at this
        omega
      have := hlen _ _ _ _ _ _ _ _ hstep j 0 (le_refl _) (by simp [WriterIface.inBank, hin])
      simp only [hj, if_false]
      omega
  · have eo : Tf = WriterIfaceJ.outBankJ (gInP Dv) (gOutP Dv) w v
        (fun j => if j = gInP Dv ∨ j = gOutP Dv then [] else Tf j) := by
      funext j
      unfold WriterIfaceJ.outBankJ
      by_cases hi : j = gInP Dv
      · subst hi
        simp only [if_true, hTf, gInP, Fin.addCases_left, ws, wt]
        rw [wenc_A_s, hIN]
      · by_cases ho : j = gOutP Dv
        · subst ho
          rw [if_neg hi, if_pos rfl]
          simp only [hTf, gOutP, Fin.addCases_left, ws, wt]
          rw [wenc_A_s, hOUT]
        · simp [hi, ho]
    rw [← eo]
    obtain ⟨r, hr, hH, hT, hs⟩ := hstep
    exact ⟨r, hr, hT, fun i => by rw [hH], hs⟩

end NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
