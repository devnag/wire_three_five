import Lean
import Proof.Wire_3_5.Foundations.OutMachineSlot0S
import Proof.Wire_3_5.Foundations.OutMachineSlot1Gen
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineSAShell
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase


noncomputable section
set_option maxRecDepth 4096


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

end Dock

/-! ## The slot-0 machine -/

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

end
