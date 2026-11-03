import Lean
import Proof.Wire_3_5.Foundations.OutMachineSwL
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SWParts
import Proof.Wire_3_5.FinalPass.SymFront3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineJoinG
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsC7
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.Foundations.OutMachineSwLABase


noncomputable section
set_option maxRecDepth 120000


/-! # SWl (root #262/#273/#278/#283), part 3: **`swL : ∀ l, SWParts.SWlT l`** (the templates' writer)

The SYM words writer's templates (slots `28 … 31`: the `symWords` word `4·3 + j` = `S3.templJ`, the stage-5 template
`levelWord M J W (blank rows of length |G_j|)` of the base list, P3:1449-1477, 1508-1520, 3170-3178) at a SYM request,
from the core's blank entry, on NW's bank `x ≥ DT + 7`:

1. The SYM front `frontM` (`front_run`, `FrontOut`: `M`, `B` in `G 32 = 440`, `G 33 = 441`, `|G_j|` in `330 + j`);
2. **`swlP`**: the low registers `0 … 55` cleared, `numsP` (part 2), `circ` (part 1) per circuit on the blank streams
   `oL j = sT (DT + 3 + j)`, every register cleared (**`swlP_spec`**, `circCap`);
3. **`swl_word`** (slot `12 + j` is `templJ`) and E's `tplWord_eq`: the written words ARE the slots.

* `lowRegs`, `oL`, `lR`, `swlP`, `tplOf`, `circCap`, `swlP_spec`, `swl_word`, `KcL`/`DkL`/`CsL`/`DsL`, `capArith`,
  `costArith`, `lM`, **`lRun`**, **`swL`**, **`swLAll`** (`Pl` of `Close7.finalPassClose7`).

Paper quantity of the main type: the SYM call's stage-5 templates (the `symWords`, kind `3`, P3:1449-1477,
3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout (LNS LNR sT)
open NearCubicWires.WireExponent3_5.FinalPass.SymParts.Tmpl (tplWord)

variable (cap : ℕ)

/-! ## The whole program -/

/-! ## The slots, the constants, the run -/

section Gate
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)

variable (l : Literals)

/-- **The templates' slots**: word `j` of `SWlT` is `templJ` (the `symWords` word `4·3 + j`). -/
theorem swl_word (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (j : Fin 4) :
    FinalPass.SWParts.swWs l 12 4 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ j =
      PrimT.S3.templJ (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) j := by
  have hj := j.isLt
  have hv : (symSlot ⟨12 + j.val, by omega⟩).val = 28 + j.val := by
    show 16 + (12 + j.val) = 28 + j.val; omega
  simp only [FinalPass.SWParts.swWs, FinalPass.Seams.frontWordsW2, FinalPass.Seams.frontWordsOfW2, dif_pos hs]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · have e2 : (⟨(symSlot ⟨12 + j.val, by omega⟩).val - 16, h3⟩ : Fin 16) = PrimT.S3.wIdx 3 j :=
      Fin.ext (by show 16 + (12 + j.val) - 16 = 4 * 3 + j.val; omega)
    show PrimT.S3.symWords _ ⟨(symSlot ⟨12 + j.val, by omega⟩).val - 16, h3⟩ = _
    rw [e2, PrimT.S3.symWords_idx]
    rfl
  · exfalso
    have e3 : FinalPass.Finish.Sw0.nw = 16 := sw0_nw
    omega

/-- SWl's capacity coefficient and degree (on `F`, `fe`). -/
noncomputable def KcL (F : GateFree l) : ℕ := FinalPass.SymFront.KF l F + 2 ^ 25 * (FinalPass.SymFront.CF l F + 10) ^ 2
noncomputable def DkL (fe : ℕ) : ℕ := FinalPass.SymFront.DF l fe + 2 * FinalPass.SymFront.DFs l fe
/-- SWl's step and residue coefficient and degree. -/
noncomputable def CsL (F : GateFree l) : ℕ := FinalPass.SymFront.CF l F + 1 + 3780000 * KcL l F ^ 3
noncomputable def DsL (fe : ℕ) : ℕ := FinalPass.SymFront.DFs l fe + 3 * DkL l fe

variable (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x)

/-- **SWl's machine** at a gate: the SYM front, then `swlP`. -/
noncomputable def lM (F : GateFree l) :=
  Composition.machine (FinalPass.SymFront.frontM x (hx3 x hx) l F) (swlP x hx).toProg.compile

/-- **SWl's run** at a SYM request. -/
theorem lRun (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (hm : FinalPass.SWParts.symG l F kclk coef A a ha r) (σ : WState (LNS x) LNR)
    (hin : σ.st (UnionMachine.NumsPh2.sIn x) = frame (fpIn l F kclk coef A a ha r)) (hsh : ∀ i, σ.sh i = 0)
    (hbl : ∀ i, i ≠ UnionMachine.NumsPh2.sIn x → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hcell : σ.cell = false) :
    ∃ (τ : WState (LNS x) LNR) (n : ℕ),
      n ≤ CsL l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsL l F.filterErrDeg ∧
      Step (lM l x hx F) n (wenc (KcL l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkL l F.filterErrDeg) σ).H
        (wenc (KcL l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkL l F.filterErrDeg) σ).A
        (wenc (KcL l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkL l F.filterErrDeg) τ).H
        (wenc (KcL l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkL l F.filterErrDeg) τ).A ∧
      (∀ k : Fin 4, τ.st (oL x hx k) = FinalPass.SWParts.swWs l 12 4 (by norm_num) F kclk coef A a ha r k) ∧
      τ.st (UnionMachine.NumsPh2.sIn x) = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ UnionMachine.NumsPh2.sIn x → (∀ k, i ≠ oL x hx k) →
        (τ.st i).length ≤ CsL l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsL l F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hm' : mode = .sym := hm
  subst hm'
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1 :=
    ⟨_, rfl⟩
  rw [← hXd]
  have hX1 : 1 ≤ X := by omega
  obtain ⟨cap, hcapd⟩ : ∃ v, v = KcL l F * X ^ DkL l F.filterErrDeg := ⟨_, rfl⟩
  rw [← hcapd]
  have hcapF : FinalPass.SymFront.KF l F * X ^ FinalPass.SymFront.DF l F.filterErrDeg +
      2 ^ 25 * (FinalPass.SymFront.CF l F * X ^ FinalPass.SymFront.DFs l F.filterErrDeg + 10) ^ 2 ≤ cap := by
    rw [hcapd]; exact capArith X _ _ _ _ hX1
  obtain ⟨τ0, m0, hm0, s0, hF⟩ := FinalPass.SymFront.front_run x (hx3 x hx) l F kclk coef A a ha ha' Cs carriers
    translation hcall cap (by rw [← hXd]; omega) σ ⟨hin, hsh, hbl, hv, hcell⟩
  rw [← hXd] at hm0 hF
  set V := FinalPass.SymFront.CF l F * X ^ FinalPass.SymFront.DFs l F.filterErrDeg with hVd
  set k := FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers with hk
  set Pl := Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers with hPl
  have hM : τ0.val 440 = Pl.M := hF.vM
  have hB : τ0.val 441 = Pl.B := hF.vB
  have hL : ∀ j : Fin 4, τ0.val (lR j) = (PrimT.S3.gatesJ k j).length := fun j => by
    rw [hk]
    dsimp only [PrimT.S3.gatesJ, FinalPass.Seams.symCallOf]
    by_cases h : j.val < a'
    · rw [dif_pos h]; exact hF.vL j h
    · rw [dif_neg h]; exact hF.vL0 j (by omega)
  obtain ⟨τ, nP, hnP, eP, hout, hoth, hsh', hval⟩ := swlP_spec cap x hx τ0 Pl.M Pl.B V
    (fun j => (PrimT.S3.gatesJ k j).length) hM hB hL hF.vle (by rw [← hB]; exact hF.vle 441)
    (by rw [← hM]; exact hF.vle 440) (fun j => by rw [← hL j]; exact hF.vle (lR j))
    (fun j => hF.hi ⟨UnionMachine.DataDock.DT + 3 + j.val, by have := j.isLt; omega⟩
      (show UnionMachine.DataDock.DT + 3 ≤ UnionMachine.DataDock.DT + 3 + j.val by omega))
    (fun j => hF.heads _) (by omega)
  have hKc : 1 ≤ KcL l F := by
    unfold KcL
    have h : 0 < 2 ^ 25 * (FinalPass.SymFront.CF l F + 10) ^ 2 :=
      Nat.mul_pos (Nat.two_pow_pos 25) (pow_pos (by omega) 2)
    omega
  have hVc : V ≤ CsL l F * X ^ DsL l F.filterErrDeg :=
    Nat.mul_le_mul (by unfold CsL; omega) (Nat.pow_le_pow_right hX1 (by unfold DsL; omega))
  refine ⟨τ, m0 + 1 + nP, ?_, Step.seq s0 (Exec.step (WExec.exec cap eP)), fun j => ?_, ?_, fun i hi hk' => ?_,
    fun i => ?_, hval⟩
  · rw [hcapd] at hnP
    exact costArith X _ _ _ _ m0 nP hX1 hKc hm0 hnP
  · rw [hout j, swl_word l F kclk coef A a ha ha' Cs carriers translation hcall hs j]
    unfold tplOf PrimT.S3.templJ
    exact FinalPass.SymParts.Tmpl.tplWord_eq Pl.base _
  · rw [hoth _ (fun j e => oL_ne x hx j e.symm)]
    exact hF.hin
  · rw [hoth i hk']
    exact (hF.resid i hi).trans hVc
  · rw [hsh']
    exact hF.heads i

/-- **SWl** (`SWParts.SWlT l`) on NW's bank `x ≥ DT + 7`. -/
noncomputable def swL : FinalPass.SWParts.SWlT l :=
  ⟨LNS x, LNR, _, fun F => lM l x hx F, UnionMachine.NumsPh2.sIn x, oL x hx, fun k => oL_ne x hx k,
    KcL l, DkL l, CsL l, DsL l,
    fun F kclk coef A a ha r hm σ hin hsh hbl hv hc => lRun l x hx F kclk coef A a ha r hm σ hin hsh hbl hv hc⟩

end Gate

/-- **`Pl`** of `Close7.finalPassClose7`: SWl at `x = DT + 7`. -/
noncomputable def swLAll : ∀ l, FinalPass.SWParts.SWlT l := fun l => swL l (UnionMachine.DataDock.DT + 7) le_rfl

end NearCubicWires.WireExponent3_5.FinalPass.Out.SwL

end
