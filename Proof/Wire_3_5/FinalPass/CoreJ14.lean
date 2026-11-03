import Lean
import Proof.Wire_3_5.FinalPass.CoreJ10
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.CoreJ11
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core over the writers with arbitrary residues, part J14: the SYM branch (P3:3170-3181)

**`stageSJ`**: the branch machine reads the mode tape `[thrFlag mode]`: at a SYM request (`false`) the SYM words writer
(`SymWordsMJ`) runs on the last block of the room and writes the SYM slots; at a THR request (`true`) nothing runs. The
room invariant reaches the room's end; the input, the reference and every tape off the room and the SYM slots are
kept.

Paper quantity: the SYM evaluator's call words (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)

section Run
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {mTh : ℕ}
  (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- The SYM branch's machine. -/
noncomputable def iteSJ :=
  iteMachine (MbJ W L hR) (Prog.skip : Prog L.t).compile
    (wstageM L hR (W.SW.M F) W.SW.sIn W.SW.sOut (outS L) (oSJ W) (hSWJ W) (TcJ W L hR))

/-- **The SYM branch.** -/
theorem stageSJ (r : FReq l F kclk coef A a ha) (c : ℕ) (A5 : Fin L.t → List Bool)
    (hin : A5 (i0 L) = frame (fpIn l F kclk coef A a ha r)) (hT : A5 (TcJ W L hR) = sent c)
    (hinv : RInv L hR c A5 (oSJ W)) (hMb : A5 (MbJ W L hR) = [thrFlag r.1.mode]) (hSo : ∀ k, A5 (outS L k) = [])
    (hKS : W.SW.Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Dk F.filterErrDeg ≤ c)
    (hSS : W.SW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Ds F.filterErrDeg ≤ c) :
    ∃ A6 : Fin L.t → List Bool,
      Step (iteSJ W F L hR) (W.SW.nr * (6 * c + 17) + 1 + 1 + 1 + W.SW.Cs F *
        ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Ds F.filterErrDeg + 1) (fun _ => 0) A5 (fun _ => 0) A6 ∧
      A6 (i0 L) = frame (fpIn l F kclk coef A a ha r) ∧ A6 (TcJ W L hR) = sent c ∧ RInv L hR c A6 (mCoreOfJ W) ∧
      (r.1.mode = .sym → ∀ k, A6 (outS L k) = frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k)) ∧
      (r.1.mode = .thr → ∀ k, A6 (outS L k) = A5 (outS L k)) ∧
      (∀ y, (∀ i, hR.coreE i ≠ y) → (∀ k, y ≠ outS L k) → A6 y = A5 y) := by
  have hiT : (iTcJ W L).val < oSJ W := by have := iTc_ltJ W L; unfold oSJ oNJ oBJ; omega
  cases hm : r.1.mode with
  | sym =>
    obtain ⟨A6, s6, a6o, a6in, a6inv, a6T, a6keep, _⟩ := wstageJ L hR (W.SW.M F) W.SW.sIn W.SW.sOut W.SW.out_ne
      (outS L) (outS_inj L) (fun k => wd_ne0 L _) (fun k i => wd_neRJ W L hR _ i) (oSJ W) (hSWJ W) (iTcJ W L) hiT c _ _
      hKS hSS _ (fun k => frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k))
      (fun σ h1 h2 h3 h4 h5 => W.SW.run F kclk coef A a ha r hm σ h1 h2 h3 h4 h5) A5 hin hSo hinv hT
    have hb : (⟨fun _ => 0, A5⟩ : Bank L.t).bit (MbJ W L hR) = false := by
      show readTapeBit (A5 (MbJ W L hR)) 0 = _; rw [hMb, hm]; rfl
    refine ⟨A6, iteM_F (MbJ W L hR) (Prog.skip : Prog L.t).compile _ ⟨fun _ => 0, A5⟩ ⟨fun _ => 0, A6⟩ _ hb s6,
      a6in, a6T, a6inv, fun _ => a6o, fun h => absurd h (by simp), a6keep⟩
  | thr =>
    have hb : (⟨fun _ => 0, A5⟩ : Bank L.t).bit (MbJ W L hR) = true := by
      show readTapeBit (A5 (MbJ W L hR)) 0 = _; rw [hMb, hm]; rfl
    have s6 := iteM_T (MbJ W L hR) (Prog.skip : Prog L.t).compile
      (wstageM L hR (W.SW.M F) W.SW.sIn W.SW.sOut (outS L) (oSJ W) (hSWJ W) (TcJ W L hR))
      ⟨fun _ => 0, A5⟩ ⟨fun _ => 0, A5⟩ 0 hb (skip_step _)
    refine ⟨A5, s6.enlarge (by omega), hin, hT, fun i => ⟨(hinv i).1, fun h => absurd i.isLt (by omega)⟩,
      fun h => absurd h (by simp), fun _ _ => rfl, fun _ _ _ => rfl⟩

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
