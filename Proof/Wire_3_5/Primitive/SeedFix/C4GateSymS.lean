import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymL
import Proof.Wire_3_5.Primitive.SeedFix.C4GatesW2

/-! # G2, the SYM gate-frame writer, part 2: the stages (P3:1655-1664, 3119-3120)

"The algorithm receives polynomial-bit integer circuit descriptions" (P3:3119-3120), and C3a's gate field is the call's
common pool "over all `2^k` rows and polynomially many original atoms" (P3:1662-1663). On part 1's layout, the writer's
five stages:

* **`dock_wm`**: a register-language program docked on an ambient bank, started from the state read off the bank
  (`stOf`: the streams from their tapes, every head and register `0`), non-stream tapes blank;
* **`front_stage`**: the front `F1 ; F2 ; F3` (the request, `1^n`, `1^W`) on the front's tapes;
* **`copy_step`**: `copyW` puts `1^W` on the data stage's `1^L` and `1^n` on the converter's arity ruler;
* **`data_stage`**: PA's data stage docked on `dS` (its entry bank `data_entry`), `data_after`;
* **`conv_stage`**: the converter (`C4Gates.convAll_spec2` over the six slots) docked on `cS`: the output tape holds
  C3a's gate field `C4Geo.gateField (allJ.flatMap Gs)`.

Paper quantity of the main type (`conv_stage`): C3a's gate field of the call's pool. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4GateSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront

/-! ## A word program docked on an ambient bank -/

section Dock
variable {ns nr u : ℕ}

/-- The start state read off an ambient bank: the streams from their tapes, every head and register `0`. -/
def stOf (sl : Fin (ns + 2 + nr + 1) → Fin u) (E : Fin u → List Bool) : WState ns nr :=
  ⟨fun _ => 0, fun i => E (sl (Fin.castAdd 1 (sTape i))), fun _ => 0, false⟩

theorem stOf_st (sl : Fin (ns + 2 + nr + 1) → Fin u) (E : Fin u → List Bool) (i : Fin (ns + 1)) :
    (stOf sl E).st i = E (sl (Fin.castAdd 1 (sTape i))) := rfl

/-- **A word program docked on an ambient bank**: from the state read off the bank (non-stream tapes blank), the
compiled program under the masked reset runs in `2c + 2` steps; its tapes' streams are the program's. -/
theorem dock_wm (cap capL : ℕ) (P : WM ns nr) (sl : Fin (ns + 2 + nr + 1) → Fin u) (hi : Function.Injective sl)
    (E : Fin u → List Bool)
    (hE : ∀ j : Fin (ns + 2 + nr + 1), (∀ i, j ≠ Fin.castAdd 1 (sTape i)) → E (sl j) = [])
    (τ : WState ns nr) (c : ℕ) (hw : WExec cap P (stOf sl E) τ c) (hc : c ≤ capL) :
    ∃ A' : Fin (ns + 2 + nr + 1) → List Bool,
      Step (RecoveryFocus.machine sl (MaskedReset.machine P.toProg.compile (fun _ => true))) (2 * c + 2)
        (fun _ => 0) E (fun _ => 0) (install sl E A') ∧ ∀ i, A' (Fin.castAdd 1 (sTape i)) = τ.st i := by
  obtain ⟨A', h, hA'⟩ := C4Pipe.wm_blank cap capL P (stOf sl E) τ c hw (fun _ => rfl) (fun _ => rfl) rfl hc
  refine ⟨A', dockZ h sl hi (fun _ => 0) E (fun _ => rfl) ?_, hA'⟩
  intro j
  refine Fin.addCases (fun a => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    rcases tape_cases a with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
    · simp only [C4Pipe.wblank, role_sTape, stOf]
    · simp only [C4Pipe.wblank, role_cTape]
      exact hE _ (fun i h => sTape_ne_c i (Fin.castAdd_injective _ _ h).symm)
    · simp only [C4Pipe.wblank, role_rTape]
      exact hE _ (fun i h => sTape_ne_r i r (Fin.castAdd_injective _ _ h).symm)
  · rw [Fin.addCases_right]
    exact hE _ (fun i h => by
      have h1 := congrArg Fin.val h
      have h2 := (sTape (nr := nr) i).isLt
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
      omega)

end Dock

/-! ## The machine -/

/-- The front: the raw request, `1^n`, `1^W`. -/
noncomputable def gsFront (Dv Cv : ℕ) := Composition.machine (Composition.machine (F1 Dv) (F2 Dv)) (F3 Dv Cv)

/-- The copy: `1^W` (stream `0`) onto stream `1`, `1^n` (stream `2`) onto stream `3`. -/
def copyW : WM 4 1 := .seq (C4Pipe.ucopy 0 1) (C4Pipe.ucopy 2 3)

/-- The converter's slots: all six. -/
def allJ : List (Fin 6) := [0, 1, 2, 3, 4, 5]

noncomputable def copyM := MaskedReset.machine copyW.toProg.compile (fun _ => true)

noncomputable def convM := MaskedReset.machine (C4Gates.convAll allJ).toProg.compile (fun _ => true)

/-- The writer before its teardown: the front, the copy, the data stage, the converter. -/
noncomputable def gsInner (Dv Cv : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (gl (Dv := Dv)) (gsFront Dv Cv)) (RecoveryFocus.machine (kS (Dv := Dv)) copyM))
    (RecoveryFocus.machine (dS (Dv := Dv)) PrimAsm.Data.dataM)) (RecoveryFocus.machine (cS (Dv := Dv)) convM)

/-- **The SYM gate-frame writer** (every head back at `0`). -/
noncomputable def gsM (Dv Cv : ℕ) := MaskedReset.machine (gsInner Dv Cv) (fun _ => true)

/-- The request port. -/
def gsIn (Dv : ℕ) : Fin (GT Dv + 1) := Fin.castAdd 1 (gl (ws gIN))

/-- The output port: the converter's output stream. -/
def gsOut (Dv : ℕ) : Fin (GT Dv + 1) := Fin.castAdd 1 (cReg 0)

theorem gsIn_ne_out (Dv : ℕ) : gsIn Dv ≠ gsOut Dv := by
  intro h
  have h1 := congrArg Fin.val h
  have e1 : (gsIn Dv).val = 0 := rfl
  have e2 : (gsOut Dv).val = GLt Dv + (DT + (8 + 0)) := rfl
  omega

/-! ## Stage 1: the front -/

section Front
variable {Dv : ℕ}

/-- The front's steps. -/
def frontC (w : List Bool) (n Dv Cv : ℕ) : ℕ :=
  2 * (2 * w.length + 1) + 2 + 1 + (2 * (8 * n + 20 * natBitLength n + 17) + 2) + 1 +
    PCPSerializerCapacity.Power.budget Dv Cv n

theorem gsFront_step (Cv n : ℕ) (w sfx : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx) :
    ∃ B3 : Fin (GLt Dv) → List Bool,
      Step (gsFront Dv Cv) (frontC w n Dv Cv) (fun _ => 0) (A0 w) (fun _ => 0) B3 ∧
      B3 (ws gIN) = frame w ∧ B3 (ws gNT) = List.replicate n true ∧
      B3 (ws gCT) = List.replicate (UnaryCalc.value Dv Cv n) true := by
  have hWT : WT = 78 := rfl
  obtain ⟨B1, s1, b1in, b1raw, b1o⟩ := f1_step (Dv := Dv) w
  have hA0 : ∀ i : Fin (GLt Dv), i ≠ ws gIN → A0 w i = [] := fun i hi => by simp [A0, hi]
  have k1 : ∀ i : Fin (GLt Dv), i.val ≠ 0 → i.val ≠ WT → i.val ≠ WT + 1 → B1 i = [] := by
    intro i h0 h1 h2
    obtain ⟨n0, n1, n2⟩ := slots1_ne i h0 h1 h2
    rw [b1o i n0 n1 n2, hA0 i n0]
  obtain ⟨B2, s2, b2nt, b2pw, b2o⟩ := f2_step (Dv := Dv) n w sfx hw B1 b1raw
    (k1 _ (by rw [ws_NT]; omega) (by rw [ws_NT]; omega) (by rw [ws_NT]; omega))
    (k1 _ (by rw [pw_val]; omega) (by rw [pw_val]; omega) (by rw [pw_val]; omega))
    (fun k => k1 _ (by rw [cp_val]; omega) (by rw [cp_val]; omega) (by rw [cp_val]; omega))
  have k2 : ∀ i : Fin (GLt Dv), i.val ≠ 0 → i.val ≠ 2 → i.val ≠ WT → i.val ≠ WT + 1 → i.val ≠ WT + 14 →
      (i.val < WT + 3 ∨ WT + 14 ≤ i.val) → B2 i = [] := by
    intro i h0 h2 h1 h11 h14 hr
    rw [b2o i (slots2_ne i h1 h2 h14 hr)]
    exact k1 i h0 h1 h11
  obtain ⟨B3, s3, b3ct, b3o⟩ := f3_step (Dv := Dv) Cv n B2 b2pw
    (k2 _ (by rw [ws_CT]; omega) (by rw [ws_CT]; omega) (by rw [ws_CT]; omega) (by rw [ws_CT]; omega)
      (by rw [ws_CT]; omega) (by rw [ws_CT]; omega))
    (fun k hk => by
      have hk0 : k.val ≠ 0 := fun e => hk (Fin.ext e)
      exact k2 _ (by rw [pw_val]; omega) (by rw [pw_val]; omega) (by rw [pw_val]; omega) (by rw [pw_val]; omega)
        (by rw [pw_val]; omega) (by rw [pw_val]; omega))
  refine ⟨B3, (s1.seq s2).seq s3, ?_, ?_, b3ct⟩
  · rw [b3o _ (slots3_ne _ (by rw [ws_IN]; omega) (by rw [ws_IN]; omega)),
      b2o _ (slots2_ne _ (by rw [ws_IN]; omega) (by rw [ws_IN]; omega) (by rw [ws_IN]; omega)
        (Or.inl (by rw [ws_IN]; omega)))]
    exact b1in
  · rw [b3o _ (slots3_ne _ (by rw [ws_NT]; omega) (by rw [ws_NT]; omega))]
    exact b2nt

/-- The writer's entry bank on its layout. -/
def gsA0 (w : List Bool) : Fin (GT Dv) → List Bool := fun i => if i = gl (ws gIN) then frame w else []

theorem gl_inj : Function.Injective (gl (Dv := Dv)) := Fin.castAdd_injective _ _

theorem gl_ne (i : Fin (GT Dv)) (h : GLt Dv ≤ i.val) : ∀ j, gl j ≠ i := by
  intro j e
  have := congrArg Fin.val e
  rw [gl_val] at this
  have := j.isLt
  omega

/-- **Stage 1**: the front on its tapes; every other tape stays blank. -/
theorem front_stage (Cv n : ℕ) (w sfx : List Bool) (hw : w = RepairRepresentation.natWord n ++ sfx) :
    ∃ E : Fin (GT Dv) → List Bool,
      Step (RecoveryFocus.machine (gl (Dv := Dv)) (gsFront Dv Cv)) (frontC w n Dv Cv) (fun _ => 0) (gsA0 w)
        (fun _ => 0) E ∧
      E (gl (ws gIN)) = frame w ∧ E (gl (ws gNT)) = List.replicate n true ∧
      E (gl (ws gCT)) = List.replicate (UnaryCalc.value Dv Cv n) true ∧ ∀ i, GLt Dv ≤ i.val → E i = [] := by
  obtain ⟨B3, s, b0, b2, b3⟩ := gsFront_step (Dv := Dv) Cv n w sfx hw
  have hA : ∀ j : Fin (GLt Dv), gsA0 (Dv := Dv) w (gl j) = A0 w j := by
    intro j
    by_cases hj : j = ws gIN
    · subst hj
      simp [gsA0, A0]
    · have hne : gl j ≠ gl (ws gIN) := fun e => hj (gl_inj e)
      simp [gsA0, A0, hj, hne]
  refine ⟨_, dockZ s gl gl_inj (fun _ => 0) (gsA0 w) (fun _ => rfl) hA, ?_, ?_, ?_, ?_⟩
  · rw [install_slot _ gl_inj]; exact b0
  · rw [install_slot _ gl_inj]; exact b2
  · rw [install_slot _ gl_inj]; exact b3
  · intro i hi
    rw [install_other _ _ _ _ (gl_ne i hi)]
    have hne : i ≠ gl (ws gIN) := fun e => by
      rw [e, gl_val] at hi
      have := (ws (Dv := Dv) gIN).isLt
      omega
    simp [gsA0, hne]

end Front

/-! ## Stage 2: the copy -/

theorem copyW_spec (cap W n : ℕ) (σ : WState 4 1) (h0 : σ.st 0 = List.replicate W true) (h1 : σ.st 1 = [])
    (h2 : σ.st 2 = List.replicate n true) (h3 : σ.st 3 = []) (hs : ∀ i, σ.sh i = 0) :
    ∃ τ : WState 4 1, WExec cap copyW σ τ (W * 7 + 1 + 1 + (n * 7 + 1)) ∧ τ.st 0 = List.replicate W true ∧
      τ.st 1 = List.replicate W true ∧ τ.st 2 = List.replicate n true ∧ τ.st 3 = List.replicate n true := by
  have e1 := C4Pipe.ucopy_spec cap 0 1 (by decide) W W 0 σ (by omega) h0 (hs 0) (by rw [h1]; rfl) (hs 1)
  obtain ⟨σ1, hσ1⟩ : ∃ x, x = ((σ.sets 1 (List.replicate W true)).seth 0 W).seth 1 W := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have a0 : σ1.st 0 = List.replicate W true := by
    rw [hσ1]; simp +decide [WState.seth, WState.sets, Function.update_apply, h0]
  have a1 : σ1.st 1 = List.replicate W true := by
    rw [hσ1]; simp +decide [WState.seth, WState.sets, Function.update_apply]
  have a2 : σ1.st 2 = List.replicate n true := by
    rw [hσ1]; simp +decide [WState.seth, WState.sets, Function.update_apply, h2]
  have a3 : σ1.st 3 = [] := by
    rw [hσ1]; simp +decide [WState.seth, WState.sets, Function.update_apply, h3]
  have b2 : σ1.sh 2 = 0 := by
    rw [hσ1]; simp +decide [WState.seth, WState.sets, Function.update_apply, hs]
  have b3 : σ1.sh 3 = 0 := by
    rw [hσ1]; simp +decide [WState.seth, WState.sets, Function.update_apply, hs]
  have e2 := C4Pipe.ucopy_spec cap 2 3 (by decide) n n 0 σ1 (by omega) a2 b2 (by rw [a3]; rfl) b3
  refine ⟨_, WExec.seq e1 e2, ?_, ?_, ?_, ?_⟩ <;>
    simp +decide [WState.seth, WState.sets, Function.update_apply, a0, a1, a2]

section Copy
variable {Dv : ℕ}

theorem kS_ne (i : Fin (GT Dv)) (h2 : i.val ≠ 2) (h3 : i.val ≠ 3) (h4 : i.val ≠ GLt Dv + 3)
    (h5 : i.val < GLt Dv + DT ∨ GLt Dv + (DT + 8) ≤ i.val) (h6 : i.val ≠ GLt Dv + (DT + 19)) :
    ∀ c, kS (Dv := Dv) c ≠ i := by
  intro c e
  have hv := congrArg Fin.val e
  rw [kS_val] at hv
  have := c.isLt
  split_ifs at hv <;> omega

/-- **Stage 2**: the copy, docked on `kS`. -/
theorem copy_step (E : Fin (GT Dv) → List Bool) (n W : ℕ) (hct : E (gl (ws gCT)) = List.replicate W true)
    (hnt : E (gl (ws gNT)) = List.replicate n true) (hlt : E (dReg (dPos PrimAsm.Data.sLT)) = [])
    (hns : E (cReg nsPos) = []) (hk : ∀ c : Fin 8, E (kReg c) = []) :
    ∃ K' : Fin 8 → List Bool,
      Step (RecoveryFocus.machine (kS (Dv := Dv)) copyM) (2 * (W * 7 + 1 + 1 + (n * 7 + 1)) + 2) (fun _ => 0) E
        (fun _ => 0) (install kS E K') ∧
      install kS E K' (dReg (dPos PrimAsm.Data.sLT)) = List.replicate W true ∧
      install kS E K' (cReg nsPos) = List.replicate n true ∧
      install kS E K' (gl (ws gCT)) = List.replicate W true ∧ install kS E K' (gl (ws gNT)) = List.replicate n true := by
  have e0 : kS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 1) (0 : Fin 5))) = gl (ws gCT) :=
    Fin.ext (by rw [kS_val]; rfl)
  have e1 : kS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 1) (1 : Fin 5))) = dReg (dPos PrimAsm.Data.sLT) :=
    Fin.ext (by rw [kS_val]; rfl)
  have e2 : kS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 1) (2 : Fin 5))) = gl (ws gNT) :=
    Fin.ext (by rw [kS_val]; rfl)
  have e3 : kS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 1) (3 : Fin 5))) = cReg nsPos :=
    Fin.ext (by rw [kS_val]; rfl)
  obtain ⟨τ, hx, t0, t1, t2, t3⟩ := copyW_spec 1 W n (stOf (ns := 4) (nr := 1) kS E)
    (by rw [stOf_st, e0, hct]) (by rw [stOf_st, e1, hlt]) (by rw [stOf_st, e2, hnt]) (by rw [stOf_st, e3, hns])
    (fun _ => rfl)
  have hE : ∀ j : Fin 8, (∀ i, j ≠ Fin.castAdd 1 (sTape (ns := 4) (nr := 1) i)) → E (kS j) = [] := by
    intro j hj
    have j0 : j.val ≠ 0 := fun h => hj 0 (Fin.ext (by rw [h]; rfl))
    have j2 : j.val ≠ 2 := fun h => hj 1 (Fin.ext (by rw [h]; rfl))
    have j3 : j.val ≠ 3 := fun h => hj 2 (Fin.ext (by rw [h]; rfl))
    have j4 : j.val ≠ 4 := fun h => hj 3 (Fin.ext (by rw [h]; rfl))
    have ek : kS (Dv := Dv) j = kReg j := Fin.ext (by rw [kS_val, kReg_val]; split_ifs <;> omega)
    rw [ek, hk]
  obtain ⟨K', s, hK'⟩ := dock_wm 1 _ copyW kS kS_inj E hE τ _ hx (le_refl _)
  refine ⟨K', s, ?_, ?_, ?_, ?_⟩
  · rw [← e1, install_slot _ kS_inj, hK', t1]
  · rw [← e3, install_slot _ kS_inj, hK', t3]
  · rw [← e0, install_slot _ kS_inj, hK', t0]
  · rw [← e2, install_slot _ kS_inj, hK', t2]

end Copy

/-! ## Stage 3: the data stage -/

section Data
variable {Dv : ℕ}

theorem dS_reg (d : Fin DT) (h0 : d.val ≠ 0) (h2 : d.val ≠ 2) (h4 : d.val ≠ 4) : dS (Dv := Dv) d = dReg d :=
  Fin.ext (by rw [dS_val, dReg_val]; split_ifs <;> omega)

theorem dS_ne (i : Fin (GT Dv)) (h0 : i.val ≠ 0) (h2 : i.val ≠ 2) (h3 : i.val ≠ 3)
    (h5 : i.val < GLt Dv ∨ GLt Dv + DT ≤ i.val) : ∀ d, dS (Dv := Dv) d ≠ i := by
  intro d e
  have hv := congrArg Fin.val e
  rw [dS_val] at hv
  have := d.isLt
  split_ifs at hv <;> omega

/-- The data stage's entry bank, read off the writer's. -/
theorem data_entry (E : Fin (GT Dv) → List Bool) (w : List Bool) (n W : ℕ)
    (h0 : E (gl (ws gIN)) = frame w) (h2 : E (gl (ws gNT)) = List.replicate n true)
    (h3 : E (dReg (dPos PrimAsm.Data.sLT)) = List.replicate W true) (h4 : E (gl (ws gCT)) = List.replicate W true)
    (hz : ∀ d : Fin DT, d.val ≠ 3 → E (dReg d) = []) :
    ∀ d, E (dS d) = Fin.addCases (PrimAsm.Data.rawIn w n W W) (fun _ : Fin 1 => List.replicate 0 false) d := by
  have hDS : PrimAsm.Data.DS = 9883 := rfl
  have hDR : PrimAsm.Data.DR = 16 := rfl
  intro d
  refine Fin.addCases (fun a => ?_) (fun k => ?_) d
  · rw [Fin.addCases_left]
    unfold PrimAsm.Data.rawIn
    by_cases a0 : a.val = 0
    · have ea : a = sTape PrimAsm.Data.sIN := Fin.ext (by rw [a0]; rfl)
      have ed : dS (Dv := Dv) (Fin.castAdd 1 a) = gl (ws gIN) :=
        Fin.ext (by rw [dS_val, Fin.val_castAdd, if_pos a0]; rfl)
      rw [if_pos ea, ed, h0]
    · have n0 : a ≠ sTape PrimAsm.Data.sIN := fun e => a0 (by rw [e]; rfl)
      rw [if_neg n0]
      by_cases a2 : a.val = 2
      · have ea : a = sTape PrimAsm.Data.sNT := Fin.ext (by rw [a2]; rfl)
        have ed : dS (Dv := Dv) (Fin.castAdd 1 a) = gl (ws gNT) :=
          Fin.ext (by rw [dS_val, Fin.val_castAdd, if_neg a0, if_pos a2]; rfl)
        rw [if_pos ea, ed, h2]
      · have n2 : a ≠ sTape PrimAsm.Data.sNT := fun e => a2 (by rw [e]; rfl)
        rw [if_neg n2]
        by_cases a3 : a.val = 3
        · have ea : a = sTape PrimAsm.Data.sLT := Fin.ext (by rw [a3]; rfl)
          have ed : dS (Dv := Dv) (Fin.castAdd 1 a) = dReg (dPos PrimAsm.Data.sLT) :=
            Fin.ext (by rw [dS_val, dReg_val, Fin.val_castAdd, if_neg a0, if_neg a2, if_neg (by omega), a3]; rfl)
          rw [if_pos ea, ed, h3]
        · have n3 : a ≠ sTape PrimAsm.Data.sLT := fun e => a3 (by rw [e]; rfl)
          rw [if_neg n3]
          by_cases a4 : a.val = 4
          · have ea : a = sTape PrimAsm.Data.sCT := Fin.ext (by rw [a4]; rfl)
            have ed : dS (Dv := Dv) (Fin.castAdd 1 a) = gl (ws gCT) :=
              Fin.ext (by rw [dS_val, Fin.val_castAdd, if_neg a0, if_neg a2, if_pos a4]; rfl)
            rw [if_pos ea, ed, h4]
          · have n4 : a ≠ sTape PrimAsm.Data.sCT := fun e => a4 (by rw [e]; rfl)
            rw [if_neg n4]
            rw [dS_reg _ (by rw [Fin.val_castAdd]; exact a0) (by rw [Fin.val_castAdd]; exact a2)
              (by rw [Fin.val_castAdd]; exact a4)]
            exact hz _ (by rw [Fin.val_castAdd]; exact a3)
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) k).val = 9901 + k.val := by
      rw [Fin.val_natAdd, hDS, hDR]
    rw [dS_reg _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
    rw [hz _ (by rw [hv]; omega)]
    rfl

/-- **Stage 3**: PA's data stage, docked on `dS`. -/
theorem data_stage (E : Fin (GT Dv) → List Bool) (w : List Bool) (n W N m : ℕ)
    (tout : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) → List Bool)
    (h : Step PrimAsm.Data.dataM N (fun _ => 0)
      (Fin.addCases (PrimAsm.Data.rawIn w n W W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)))
    (h0 : E (gl (ws gIN)) = frame w) (h2 : E (gl (ws gNT)) = List.replicate n true)
    (h3 : E (dReg (dPos PrimAsm.Data.sLT)) = List.replicate W true) (h4 : E (gl (ws gCT)) = List.replicate W true)
    (hz : ∀ d : Fin DT, d.val ≠ 3 → E (dReg d) = []) :
    Step (RecoveryFocus.machine (dS (Dv := Dv)) PrimAsm.Data.dataM) N (fun _ => 0) E (fun _ => 0)
      (install dS E (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))) :=
  dockZ h dS dS_inj (fun _ => 0) E (fun _ => rfl) (data_entry E w n W h0 h2 h3 h4 hz)

theorem addCases_dPos (tout : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) → List Bool) (L : Fin 1 → List Bool)
    (s : Fin (PrimAsm.Data.DS + 1)) : Fin.addCases (motive := fun _ => List Bool) tout L (dPos s) = tout (sTape s) := by
  unfold dPos
  rw [Fin.addCases_left]

/-- After the data stage: the request, the slot tables, the converter's region untouched. -/
theorem data_after (E : Fin (GT Dv) → List Bool) (T' : Fin DT → List Bool) :
    install dS E T' (gl (ws gIN)) = T' (dPos PrimAsm.Data.sIN) ∧
    (∀ j : Fin 6, install dS E T' (dReg (dPos (tabStream j))) = T' (dPos (tabStream j))) ∧
    (∀ x : Fin 34, install dS E T' (cReg x) = E (cReg x)) := by
  refine ⟨?_, fun j => ?_, fun x => ?_⟩
  · have e : dS (Dv := Dv) (dPos PrimAsm.Data.sIN) = gl (ws gIN) := by unfold dS; rw [if_pos rfl]
    rw [← e, install_slot _ dS_inj]
  · have hv := tabStream_val j
    have hpos : 17 ≤ (tabStream j).val := by rw [hv]; split_ifs <;> omega
    have hp : (dPos (tabStream j)).val = (tabStream j).val + 1 := by rw [dPos_val]; split_ifs <;> omega
    have e : dS (Dv := Dv) (dPos (tabStream j)) = dReg (dPos (tabStream j)) :=
      dS_reg _ (by rw [hp]; omega) (by rw [hp]; omega) (by rw [hp]; omega)
    rw [← e, install_slot _ dS_inj]
  · have hG : 16 ≤ GLt Dv := by show 16 ≤ 78 + (14 + (14 + 2 * Dv)); omega
    have hv := cReg_val (Dv := Dv) x
    exact install_other _ _ _ _ (dS_ne _ (by omega) (by omega) (by omega) (Or.inr (by omega)))

end Data

/-! ## Stage 4: the converter -/

section Conv
variable {Dv : ℕ}

theorem cS_other (x : Fin 34) (hx : ¬(2 ≤ x.val ∧ x.val < 8)) : cS (Dv := Dv) x = cReg x := by
  unfold cS
  rw [dif_neg hx]

theorem cS_tbl (j : Fin 6) :
    cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) (C4Gates.tbl j))) = dReg (dPos (tabStream j)) := by
  apply Fin.ext
  have hv : (Fin.castAdd 1 (sTape (nr := 20) (C4Gates.tbl j))).val = j.val + 2 := by
    show (if j.val + 1 = 0 then 0 else j.val + 1 + 1) = j.val + 2
    split_ifs <;> omega
  rw [cS_val, hv, dReg_val, dPos_val, tabStream_val]
  have := j.isLt
  split_ifs <;> omega

theorem cS_ne (i : Fin (GT Dv)) (h : i.val < GLt Dv) : ∀ c, cS (Dv := Dv) c ≠ i := by
  intro c e
  have hv := congrArg Fin.val e
  rw [cS_val] at hv
  split_ifs at hv <;> omega

/-- **Stage 4**: the converter over the six slots, docked on `cS`: C3a's gate field on the output tape. -/
theorem conv_stage (E : Fin (GT Dv) → List Bool) (n H : ℕ) (Gs : Fin 6 → List (NormalizedThresholdGate n))
    (hs : Fin 6 → ℕ) (hns : E (cReg nsPos) = List.replicate n true)
    (hz : ∀ x : Fin 34, x.val ≠ 11 → E (cReg x) = [])
    (hT : ∀ j, E (dReg (dPos (tabStream j))) = FinalPass.Corner.gatesW (hs j) (Gs j) ∨
      (E (dReg (dPos (tabStream j))) = [] ∧ Gs j = []))
    (hH : ∀ j, 1 ≤ hs j ∧ hs j ≤ H ∧ ∀ g ∈ Gs j, C4Gates.GB (hs j) g) :
    ∃ E' : Fin (GT Dv) → List Bool,
      Step (RecoveryFocus.machine (cS (Dv := Dv)) convM) (2 * C4Gates.convCost n (allJ.flatMap Gs).length H + 2)
        (fun _ => 0) E (fun _ => 0) E' ∧
      E' (cReg 0) = C4Geo.gateField (allJ.flatMap Gs) ∧ ∀ i : Fin (GT Dv), i.val < GLt Dv → E' i = E i := by
  have hsO : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sO)) = cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sO)) :=
    cS_other _ (by decide)
  have hsS : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sS)) = cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sS)) :=
    cS_other _ (by decide)
  have hsQ : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sNQ)) = cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sNQ)) :=
    cS_other _ (by decide)
  have hsT : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sTS)) = cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sTS)) :=
    cS_other _ (by decide)
  have hsN : cS (Dv := Dv) nsPos = cReg nsPos := cS_other _ (by decide)
  have hE : ∀ j : Fin 34, (∀ i, j ≠ Fin.castAdd 1 (sTape (ns := 11) (nr := 20) i)) → E (cS j) = [] := by
    intro j hj
    have j0 : j.val ≠ 0 := fun h => hj 0 (Fin.ext (by rw [h]; rfl))
    have jm : ¬(2 ≤ j.val ∧ j.val ≤ 12) := fun ⟨a, b⟩ => hj ⟨j.val - 1, by omega⟩
      (Fin.ext (by show j.val = if j.val - 1 = 0 then 0 else j.val - 1 + 1; split_ifs <;> omega))
    rw [cS_other j (by omega)]
    exact hz j (by omega)
  obtain ⟨τ, c, hx, hc, hO⟩ := C4Gates.convAll_spec2
    (2 * (((allJ.flatMap Gs).length + 1) * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)) +
      8 * n + 8 * natBitLength n + 8 * natBitLength (allJ.flatMap Gs).length + 2 * H + 100) (by omega)
    H Gs hs allJ (by decide) (stOf (ns := 11) (nr := 20) cS E) (fun _ => rfl) (fun _ => rfl)
    (by rw [stOf_st]; show E (cS nsPos) = _; rw [hsN, hns])
    (by rw [stOf_st, hsO]; exact hz _ (by decide))
    (by rw [stOf_st, hsS]; exact hz _ (by decide))
    (by rw [stOf_st, hsQ]; exact hz _ (by decide))
    (by rw [stOf_st, hsT]; exact hz _ (by decide))
    (fun j _ => by rw [stOf_st, cS_tbl]; exact hT j) (fun j _ => hH j) (le_refl _)
  obtain ⟨A', s, hA'⟩ := dock_wm _ c (C4Gates.convAll allJ) cS cS_inj E hE τ c hx (le_refl c)
  have e0 : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sO)) = cReg 0 := by
    rw [hsO]; exact congrArg cReg (Fin.ext rfl)
  refine ⟨_, s.enlarge (by omega), ?_, fun i hi => install_other _ _ _ _ (cS_ne i hi)⟩
  rw [← e0, install_slot _ cS_inj, hA', hO]

end Conv

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym
