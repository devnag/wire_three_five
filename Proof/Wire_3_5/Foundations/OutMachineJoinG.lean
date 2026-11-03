import Lean
import Proof.Wire_3_5.Foundations.OutMachineJoinWBase
import Proof.Wire_3_5.FinalPass.Asm1Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase


noncomputable section
set_option maxRecDepth 4096


/-! # Writer combinators with a guard

Some writers run only at some requests (the SYM parts: `r.1.mode = .sym`). A **guarded** writer
`Finish.GuardedWordsMJ l G m ws` is `CoreWordsMJ` whose run assumes `G r`. Here:

* the raw joint layout (`jnsR`, `e1R`, `e2R`, `f2R`, `g1R`, `g2R`, `sOutR`, `jMachR`), `RunAt` (a writer's run at one
  request, abstractly), **`join_core`** (two runs at one request are the joint machine's run), `RunAt.mono`;
* **`GuardedWordsMJ.join`** (the guard shared), **`.reindex`**, **`.congrWs`**, **`.sub`**;
* **`CoreWordsMJ.toG`** (any guard), **`SymWordsMJ.ofG`** (at `G := r.1.mode = .sym` and the SYM slots' words).

Paper quantity of the main type: the front's words at a request (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.JoinG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Out.Join

section Raw

end Raw

end NearCubicWires.WireExponent3_5.FinalPass.Out.JoinG

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Out.Join NearCubicWires.WireExponent3_5.FinalPass.Out.JoinG

/-- **A guarded word writer**: `CoreWordsMJ` whose run assumes the guard `G r`. -/
structure GuardedWordsMJ (l : Literals)
    (G : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Prop) (m : ℕ)
    (ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool)
    where
  ns : ℕ
  nr : ℕ
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (ns + 2 + nr) (s F)
  sIn : Fin (ns + 1)
  sOut : Fin m ↪ Fin (ns + 1)
  out_ne : ∀ k, sOut k ≠ sIn
  Kc : GateFree l → ℕ
  Dk : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
    G F kclk coef A a ha r → ∀ σ : WState ns nr, σ.st sIn = frame (fpIn l F kclk coef A a ha r) → (∀ i, σ.sh i = 0) →
      (∀ i, i ≠ sIn → σ.st i = []) → (∀ q, σ.val q = 0) → σ.cell = false →
      ∃ (τ : WState ns nr) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).A
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).A ∧
        (∀ k : Fin m, τ.st (sOut k) = ws F kclk coef A a ha r k) ∧
        τ.st sIn = frame (fpIn l F kclk coef A a ha r) ∧
        (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) →
          (τ.st i).length ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

variable {l : Literals}
  {G : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Prop} {m m' : ℕ}
  {ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
  {ws' : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m' → List Bool}

/-- **Two guarded writers as one** (the guard shared). -/
noncomputable def GuardedWordsMJ.join (W : GuardedWordsMJ l G m ws) (W' : GuardedWordsMJ l G m' ws') :
    GuardedWordsMJ l G (m + m') fun F kclk coef A a ha r =>
      Fin.append (ws F kclk coef A a ha r) (ws' F kclk coef A a ha r) where
  ns := jnsR W.ns W'.ns
  nr := jnrR W.nr W'.nr
  s := fun F => (jMachR (W.M F) (W'.M F) W.sIn W'.sIn).1
  M := fun F => (jMachR (W.M F) (W'.M F) W.sIn W'.sIn).2
  sIn := e1R W.ns W'.ns W.sIn
  sOut := ⟨sOutR W.sOut W'.sOut, sOutR_inj _ _ W.sOut.injective W'.sOut.injective⟩
  out_ne := sOutR_ne W.sIn W.sOut W'.sOut W.out_ne
  Kc := fun F => W.Kc F + W'.Kc F
  Dk := fun e => W.Dk e + W'.Dk e
  Cs := fun F => W.Cs F + W'.Cs F + 4
  Ds := fun e => W.Ds e + W'.Ds e
  run := fun F kclk coef A a ha r hG =>
    RunAt.mono (join_core (W.M F) (W'.M F) W.sIn W.sOut W'.sIn W'.sOut W.out_ne W'.out_ne _ _ _ _ _
      (Nat.mul_le_mul (Nat.le_add_right _ _) (pow_mono_add _ _ _))
      (Nat.mul_le_mul (Nat.le_add_left _ _) (pow_mono_add' _ _ _)) _ _ _
      (W.run F kclk coef A a ha r hG) (W'.run F kclk coef A a ha r hG))
      (bndG _ _ _ _ _ (pow_mono_add _ _ _) (pow_mono_add' _ _ _))

/-- **A guarded writer at an equal word family** (on the guard). -/
noncomputable def GuardedWordsMJ.congrWs
    {ws2 : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
    (W : GuardedWordsMJ l G m ws)
    (h : ∀ F kclk coef A a ha r, G F kclk coef A a ha r → ∀ k, ws F kclk coef A a ha r k = ws2 F kclk coef A a ha r k) :
    GuardedWordsMJ l G m ws2 where
  ns := W.ns
  nr := W.nr
  s := W.s
  M := W.M
  sIn := W.sIn
  sOut := W.sOut
  out_ne := W.out_ne
  Kc := W.Kc
  Dk := W.Dk
  Cs := W.Cs
  Ds := W.Ds
  run := fun F kclk coef A a ha r hG σ hin hsh hbl hv hc => by
    obtain ⟨τ, n, hn, hs, ho, hk, hr, hτs, hτv⟩ := W.run F kclk coef A a ha r hG σ hin hsh hbl hv hc
    exact ⟨τ, n, hn, hs, fun k => (ho k).trans (h F kclk coef A a ha r hG k), hk, hr, hτs, hτv⟩

/-- **The SYM words writer from a guarded one** at `G := r.1.mode = .sym` and the SYM slots' words. -/
noncomputable def SymWordsMJ.ofG
    (W : GuardedWordsMJ l (fun _ _ _ _ _ _ r => r.1.mode = .sym) 17
      (fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k))) : SymWordsMJ l where
  ns := W.ns
  nr := W.nr
  s := W.s
  M := W.M
  sIn := W.sIn
  sOut := W.sOut
  out_ne := W.out_ne
  Kc := W.Kc
  Dk := W.Dk
  Cs := W.Cs
  Ds := W.Ds
  run := fun F kclk coef A a ha r hm => W.run F kclk coef A a ha r hm

end NearCubicWires.WireExponent3_5.FinalPass.Finish

end
