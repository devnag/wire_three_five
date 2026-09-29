import Proof.Wire_3_5.Foundations.OutMachineSlot0S
import Proof.Wire_3_5.Foundations.OutMachineSlot1Gen

/-! # SA's slot 0, part 4: the writer, and SA

* `setSt`, **`dock_streams`**: a machine's clean run (heads `0` at both ends) docked onto streams of a `WState`
  bank (`Block.dockKeep`), the bank's encoding at the other end;
* `stepReady` (a ready run is a `Step`), `s0_cases` (every slot-0 stream is `I0`, `U0` or a geo tape);
* the slot-0 machine `slot0M cr` (the trim ; the geo writer `geoM (offW cr) flD (flCv cr)` docked on `gs`), its
  constants `Cs0`, `Ds0`;
* **`slot0W l : CoreWordsMJ l 1 (SA.slot0Ws l)`** (S4's word 0, the offset word, at every request);
* **`SA.sa l : S4WordsMAJ l`** `:= SA.saOf l (slot0W l)` — **SA done**.

Paper quantity of the main type: S4's words 0–3 (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GLt gInP gOutP geoM gInP_ne_out)
open NearCubicWires.WireExponent3_5.PrimT.FlipsPack (flD flCv cA dA)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Docking a clean run onto streams -/

section Dock
variable {ns nr : ℕ}

open Classical in
/-- The bank with the streams `gsl j` replaced by `v j`. -/
noncomputable def setSt {k : ℕ} (σ : WState ns nr) (gsl : Fin k → Fin (ns + 1)) (v : Fin k → List Bool) :
    WState ns nr :=
  ⟨σ.sh, fun i => if h : ∃ j, gsl j = i then v h.choose else σ.st i, σ.val, σ.cell⟩

theorem setSt_in {k : ℕ} (σ : WState ns nr) (gsl : Fin k → Fin (ns + 1)) (hinj : Function.Injective gsl)
    (v : Fin k → List Bool) (j : Fin k) : (setSt σ gsl v).st (gsl j) = v j := by
  have h : ∃ j', gsl j' = gsl j := ⟨j, rfl⟩
  simp only [setSt]
  rw [dif_pos h, hinj h.choose_spec]

theorem setSt_off {k : ℕ} (σ : WState ns nr) (gsl : Fin k → Fin (ns + 1)) (v : Fin k → List Bool) (i : Fin (ns + 1))
    (hi : ∀ j, gsl j ≠ i) : (setSt σ gsl v).st i = σ.st i := by
  simp only [setSt]
  rw [dif_neg (fun ⟨j, hj⟩ => hi j hj)]

/-- **A clean run docked onto streams.** -/
theorem dock_streams {k s : ℕ} (M : Machine k s) (gsl : Fin k → Fin (ns + 1)) (hinj : Function.Injective gsl)
    (c n : ℕ) (σ : WState ns nr) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ q, σ.val q = 0) (tin tout : Fin k → List Bool)
    (htin : ∀ j, σ.st (gsl j) = tin j) (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) :
    Step (RecoveryFocus.machine (fun j => sTape (nr := nr) (gsl j)) M) n (wenc c σ).H (wenc c σ).A
      (wenc c (setSt σ gsl tout)).H (wenc c (setSt σ gsl tout)).A := by
  have hsi : Function.Injective (fun j => sTape (nr := nr) (gsl j)) := fun a b e => hinj (sTape_inj e)
  have hd := Block.dockKeep h (fun j => sTape (nr := nr) (gsl j)) hsi (wenc c σ).H (wenc c σ).A
    (fun j => by rw [wenc_H_s, hsh]) (fun j => by rw [wenc_A_s, htin])
  have eH : (wenc c (setSt σ gsl tout)).H = (wenc c σ).H := by
    rw [Join.wencH0 c σ hsh hv, Join.wencH0 c (setSt σ gsl tout) hsh hv]
  have eA : install (fun j => sTape (nr := nr) (gsl j)) (wenc c σ).A tout = (wenc c (setSt σ gsl tout)).A := by
    funext y
    by_cases hy : ∃ j, sTape (nr := nr) (gsl j) = y
    · obtain ⟨j, rfl⟩ := hy
      rw [install_slot _ hsi, wenc_A_s, setSt_in σ gsl hinj]
    · have hy' : ∀ j, sTape (nr := nr) (gsl j) ≠ y := fun j e => hy ⟨j, e⟩
      rw [install_other _ _ _ _ hy']
      rcases tape_cases y with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, wenc_A_s, setSt_off σ gsl tout i (fun j e => hy' j (by rw [e]))]
      · rw [wenc_A_c, wenc_A_c]; rfl
      · rw [wenc_A_r, wenc_A_r]; rfl
  rw [eH, ← eA]
  exact hd

end Dock

theorem stepReady {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

theorem s0_cases (i : Fin (S0ns + 1)) : i = I0 ∨ i = U0 ∨ ∃ j, gs j = i := by
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases h1 : i.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · refine Or.inr (Or.inr ⟨⟨i.val - 2, ?_⟩, Fin.ext ?_⟩)
      · have := i.isLt; have h2 := S0ns_eq; omega
      · show 2 + (i.val - 2) = i.val; omega

/-! ## The slot-0 machine -/

/-- **The slot-0 machine**: the trim, then the offset writer on the geo tapes. -/
noncomputable def slot0Mach (cr : ℕ) : (s : ℕ) × Machine (S0ns + 2 + 17) s :=
  ⟨_, Composition.machine trimP.toProg.compile
    (RecoveryFocus.machine (fun j => sTape (nr := 17) (gs j)) (geoM (offW cr) flD (flCv cr)))⟩

/-- The slot-0 writer's step coefficient (on the row constant) and degree. -/
noncomputable def Cs0 (cr : ℕ) : ℕ := 3001 + (cA + 100) * (cr + 1) ^ (dA + 1)
noncomputable def Ds0 : ℕ := dA + 3

theorem bound0 (N cr n1 B : ℕ) (h1 : n1 ≤ 3000 * (N + 1) ^ 2) (hB : B ≤ (cA + 100) * (N + cr + 1) ^ (dA + 1)) :
    n1 + 1 + B ≤ Cs0 cr * (N + 1) ^ Ds0 ∧ B ≤ Cs0 cr * (N + 1) ^ Ds0 := by
  have e1 : (N + 1) ^ 2 ≤ (N + 1) ^ Ds0 := Nat.pow_le_pow_right (by omega) (by unfold Ds0; omega)
  have e2 : (N + 1) ^ (dA + 1) ≤ (N + 1) ^ Ds0 := Nat.pow_le_pow_right (by omega) (by unfold Ds0; omega)
  have e3 : N + cr + 1 ≤ (cr + 1) * (N + 1) := by nlinarith
  have e4 : (N + cr + 1) ^ (dA + 1) ≤ (cr + 1) ^ (dA + 1) * (N + 1) ^ (dA + 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left e3 _
  have e5 : 1 ≤ (N + 1) ^ Ds0 := Nat.one_le_pow _ _ (by omega)
  have e6 : (cA + 100) * (N + cr + 1) ^ (dA + 1) ≤ (cA + 100) * (cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0 := by
    calc (cA + 100) * (N + cr + 1) ^ (dA + 1) ≤ (cA + 100) * ((cr + 1) ^ (dA + 1) * (N + 1) ^ (dA + 1)) :=
          Nat.mul_le_mul_left _ e4
      _ ≤ (cA + 100) * ((cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ = (cA + 100) * (cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0 := by ring
  have e7 : Cs0 cr * (N + 1) ^ Ds0 = 3001 * (N + 1) ^ Ds0 + (cA + 100) * (cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0 := by
    unfold Cs0; ring
  constructor <;> omega

/-- **The offset word's writer** (S4's word 0) at every request. -/
noncomputable def slot0W (l : Literals) : CoreWordsMJ l 1 (SA.slot0Ws l) where
  ns := S0ns
  nr := 17
  s := fun F => (slot0Mach (gate0 l F).row.cr).1
  M := fun F => (slot0Mach (gate0 l F).row.cr).2
  sIn := I0
  sOut := ⟨fun _ => Out0, fun a b _ => Subsingleton.elim a b⟩
  out_ne := fun _ => gs_ne_I _
  Kc := fun _ => 28
  Dk := fun _ => 1
  Cs := fun F => Cs0 (gate0 l F).row.cr
  Ds := fun _ => Ds0
  run := fun F kclk coef A a ha r σ hin hsh hbl hv _ => by
    set cr := (gate0 l F).row.cr with hcr
    set sfx := seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1 with hsfx
    have hfp : fpIn l F kclk coef A a ha r = r.1.word ++ sfx := rfl
    have hs := SA.starAt l r
    set P := (callInputs l F kclk coef A a ha).starParams r.1.n hs with hP
    -- the trim
    obtain ⟨τ1, n1, hx1, hn1, h1I, h1T, h1U, h1bl, h1sh, h1v⟩ := trim_spec
      (28 * ((fpIn l F kclk coef A a ha r).length + 1) ^ 1) r.1 sfx σ (by rw [hin, hfp]) hbl hsh hv
      (by rw [hfp, pow_one])
    -- the offset writer
    obtain ⟨J, hJ, hrun⟩ := offRun cr P rfl r.1 rfl r.2.2.2.2.2.1.1 r.2.2.2.2.2.1.2
      (PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha r.1 r.2)
    have hd := dock_streams (geoM (offW cr) flD (flCv cr)) gs gs_inj
      (28 * ((fpIn l F kclk coef A a ha r).length + 1) ^ 1) _ τ1 h1sh h1v
      (PrimAsm.WriterIface.inBank (gInP flD) r.1.word) _ (fun j => by
        unfold PrimAsm.WriterIface.inBank
        by_cases hj : j = gInP flD
        · subst hj; rw [if_pos rfl]; exact h1T
        · rw [if_neg hj]
          exact h1bl (gs j) (gs_ne_I j) (gs_ne_U j) (fun e => hj (gs_inj e)))
      (stepReady hrun)
    set τ := setSt τ1 gs (PrimAsm.WriterIfaceJ.outBankJ (gInP flD) (gOutP flD) r.1.word (frame (offWord P r.1)) J)
      with hτ
    have hN := FpInLen.n_le_fpIn r
    have hwN : r.1.word.length ≤ (fpIn l F kclk coef A a ha r).length := by rw [hfp, List.length_append]; omega
    have hB := offBud_le r.1 P cr ((fpIn l F kclk coef A a ha r).length + cr) (by show r.1.n ≤ _; omega)
      (by omega) (by omega) r.2.2.2.2.2.1.1 r.2.2.2.2.2.1.2
    obtain ⟨b1, b2⟩ := bound0 (fpIn l F kclk coef A a ha r).length cr n1 (offBud r.1 P cr) (by rw [hfp]; exact hn1)
      (by rw [show (fpIn l F kclk coef A a ha r).length + cr + 1 = (fpIn l F kclk coef A a ha r).length + cr + 1
        from rfl]; exact hB)
    have hOut : τ.st Out0 = frame (offWord P r.1) := by
      rw [hτ, show Out0 = gs (gOutP flD) from rfl, setSt_in τ1 gs gs_inj]
      unfold PrimAsm.WriterIfaceJ.outBankJ
      rw [if_neg (Ne.symm (gInP_ne_out flD)), if_pos rfl]
    refine ⟨τ, n1 + 1 + offBud r.1 P cr, b1, Step.seq (Exec.step (WExec.exec _ hx1)) hd, fun k => ?_, ?_, ?_,
      fun i => h1sh i, fun q => h1v q⟩
    · show τ.st Out0 = _
      rw [hOut, SA.slot0Ws_eq, frame_eq_frameP]; rfl
    · rw [hτ, setSt_off τ1 gs _ I0 (fun j => gs_ne_I j), h1I, hin]
    · intro i h1 h2
      have hO2 : i ≠ Out0 := h2 0
      rcases s0_cases i with rfl | rfl | ⟨j, rfl⟩
      · exact absurd rfl h1
      · rw [hτ, setSt_off τ1 gs _ U0 (fun j => gs_ne_U j)]
        have := Slot1.natWord_pos r.1.n
        rw [hfp] at b2 ⊢
        have hsq : 2 * (r.1.word ++ sfx).length + 1 ≤ Cs0 cr * ((r.1.word ++ sfx).length + 1) ^ Ds0 := by
          have e1 : (r.1.word ++ sfx).length + 1 ≤ ((r.1.word ++ sfx).length + 1) ^ Ds0 :=
            Nat.le_self_pow (by unfold Ds0; omega) _
          have e2 : 2 * ((r.1.word ++ sfx).length + 1) ^ Ds0 ≤ Cs0 cr * ((r.1.word ++ sfx).length + 1) ^ Ds0 :=
            Nat.mul_le_mul_right _ (by unfold Cs0; omega)
          omega
        exact le_trans h1U hsq
      · rw [hτ, setSt_in τ1 gs gs_inj]
        unfold PrimAsm.WriterIfaceJ.outBankJ
        by_cases hjI : j = gInP flD
        · subst hjI
          rw [if_pos rfl, Slot1.frame_length]
          rw [hfp] at b2 ⊢
          have e1 : (r.1.word ++ sfx).length + 1 ≤ ((r.1.word ++ sfx).length + 1) ^ Ds0 :=
            Nat.le_self_pow (by unfold Ds0; omega) _
          have e2 : 2 * ((r.1.word ++ sfx).length + 1) ^ Ds0 ≤ Cs0 cr * ((r.1.word ++ sfx).length + 1) ^ Ds0 :=
            Nat.mul_le_mul_right _ (by unfold Cs0; omega)
          have e3 : r.1.word.length ≤ (r.1.word ++ sfx).length := by rw [List.length_append]; omega
          omega
        · have hjO : j ≠ gOutP flD := fun e => hO2 (by rw [e]; rfl)
          rw [if_neg hjI, if_neg hjO]
          exact le_trans (hJ j) b2

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SA
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- **SA** (S4's words 0–3 at the bounded-residue contract): the offset writer, the sample writer, the carrier
tables. -/
noncomputable def sa (l : Literals) : S4WordsMAJ l := saOf l (Slot0.slot0W l)

end NearCubicWires.WireExponent3_5.FinalPass.Out.SA
