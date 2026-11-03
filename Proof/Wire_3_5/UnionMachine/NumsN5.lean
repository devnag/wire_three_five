import Lean
import Proof.Wire_3_5.UnionMachine.NumsN4
import Proof.Wire_3_5.UnionMachine.NumsN2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SWParts
import Proof.Wire_3_5.FinalPass.SymFront3
import Proof.Wire_3_5.FinalPass.SymFront6
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineJoinG
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsC7
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.UnionMachine.NumsN5Base


noncomputable section
set_option maxRecDepth 120000


/-! # SWn, part 5: the numbers' writer `swN x hx Kt Et tp htp l : SWParts.SWnT l` (x ≥ DT + 8)

P3:3170-3178 (the `symNums`: the SYM call's eighteen numbers, as a unary list, the SYM slot `32`): at a SYM request,
from the core's blank entry, on NW's bank `x ≥ DT + 8`:

1. The SYM front (`SymFront.frontM`, `front_runB`: the flat list's numbers, `J`, the walk length, the population
   lengths and the gate tables);
2. The post program `postN x hx tp` (`postRun`: the gate tables' widths, the tables' lengths, the templates'
   lengths `tp` (with `TplIface Kt Et tp`), the unary list on the output stream `oOut`, every register cleared).

The capacity `Kn5 F·(|fpIn|+1)^{Dn5 fe}` (above the front's need and the post program's `capP Kt Et (C_F·X^{D_Fs})`),
the steps and the residues `Cs5 F·(|fpIn|+1)^{Ds5 fe}` (degrees on `l`, `Et` and `fe` only; coefficients on `l`, `Kt`,
`Et` and the gate).

* `cap5_arith`, `cost5_arith` (pure bounds); `Kn5`, `Dn5`, `Cs5`, `Ds5`; `sO5`; `swnM`; **`swnRun`**, **`swN`**.

Paper quantity of the main type: the SYM call numbers `symNums k` (the unary list of the eighteen numbers, P3:3170-3178)
at every SYM request, on the writer's output stream, in time polynomial in the input. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

/-! ## Arithmetic -/

/-! ## The constants -/

section Consts
variable (l : Literals)

/-- **The register capacity's coefficient** (on the gate, `Kt`, `Et`). -/
noncomputable def Kn5 (Kt Et : ℕ) (F : GateFree l) : ℕ :=
  FinalPass.SymFront.KF l F + 100 * (Kt + 8) * (3 * (FinalPass.SymFront.CF l F + 2)) ^ (Et + 3)

/-- **The register capacity's degree** (on the filter degree and `Et`). -/
noncomputable def Dn5 (Et fe : ℕ) : ℕ := FinalPass.SymFront.DF l fe + FinalPass.SymFront.DFs l fe * (Et + 3)

/-- The steps' and the residues' coefficient. -/
noncomputable def Cs5 (Kt Et : ℕ) (F : GateFree l) : ℕ := FinalPass.SymFront.CF l F + 4000 * Kn5 l Kt Et F + 4001

/-- The steps' and the residues' degree. -/
noncomputable def Ds5 (Et fe : ℕ) : ℕ := Dn5 l Et fe + FinalPass.SymFront.DFs l fe

end Consts

/-! ## The machine and its run -/

section Gate
variable (x : ℕ) (hx : DataDock.DT + 8 ≤ x) (l : Literals) (Kt Et : ℕ)
  (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr)

/-- **SWn's machine** at a gate: the SYM front, then the post program. -/
noncomputable def swnM (F : GateFree l) :=
  Composition.machine (FinalPass.SymFront.frontM x (dt3 hx) l F) (postN x hx tp).toProg.compile

/-- **SWn's run at a SYM request**: the unary list of the eighteen call numbers on the output stream. -/
theorem swnRun (htp : TplIface Kt Et tp) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (σ : St x)
    (hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ sIn x → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hc : σ.cell = false) :
    ∃ (τ : St x) (m : ℕ),
      m ≤ Cs5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length
        + 1) ^ Ds5 l Et F.filterErrDeg ∧
      Step (swnM x hx l tp F) m
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) σ).H
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) σ).A
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) τ).H
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) τ).A ∧
      (∀ k : Fin 1, τ.st (sO5 x hx k) = FinalPass.SWParts.swWs l 16 1 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ k) ∧
      τ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) ∧
      (∀ i, i ≠ sIn x → (∀ k, i ≠ sO5 x hx k) →
        (τ.st i).length ≤ Cs5 l Kt Et F * ((fpIn l F kclk coef A a ha
          ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Ds5 l Et F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
    hcall⟩).length + 1 := ⟨_, rfl⟩
  rw [← hXd]
  have hX : 1 ≤ X := by omega
  obtain ⟨hcF, hcP⟩ := cap5_arith Kt Et (FinalPass.SymFront.KF l F) (FinalPass.SymFront.CF l F) X
    (FinalPass.SymFront.DF l F.filterErrDeg) (FinalPass.SymFront.DFs l F.filterErrDeg) hX
  obtain ⟨τ0, m, hm, sF, hF⟩ := FinalPass.SymFront.front_runB x (dt3 hx) l F kclk coef A a ha ha' Cs carriers
    translation hcall (Kn5 l Kt Et F * X ^ Dn5 l Et F.filterErrDeg) (by rw [← hXd]; exact hcF) σ
    ⟨hin, hsh, hbl, hv, hc⟩
  rw [← hXd] at hm hF
  obtain ⟨τ, c, eP, hc', hout, hin', hres, hsh', hv', -⟩ := postRun x hx Kt Et tp htp
    (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers)
    (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
    (FinalPass.SymFront.CF l F * X ^ FinalPass.SymFront.DFs l F.filterErrDeg)
    (Kn5 l Kt Et F * X ^ Dn5 l Et F.filterErrDeg) τ0 hF hcP
  obtain ⟨hM, hK⟩ := cost5_arith (FinalPass.SymFront.CF l F) (Kn5 l Kt Et F) X
    (FinalPass.SymFront.DFs l F.filterErrDeg) (Dn5 l Et F.filterErrDeg) m c hX hm hc'
  refine ⟨τ, m + 1 + c, hM, Step.seq sF (Exec.step (WExec.exec _ eP)), fun k => ?_, hin',
    fun i h1 h2 => (hres i h1 (h2 0)).trans hK, hsh', hv'⟩
  exact hout.trans (by rw [Subsingleton.elim k 0]; exact
    (swn_word l F kclk coef A a ha ha' Cs carriers translation hcall hs).symm)

/-- **SWn** (`SWParts.SWnT l`) on NW's bank `x ≥ DT + 8`, the template length program `tp` with its interface. -/
noncomputable def swN (htp : TplIface Kt Et tp) : FinalPass.SWParts.SWnT l :=
  ⟨LNS x, LNR, _, fun F => swnM x hx l tp F, sIn x, sO5 x hx, sO5_ne x hx,
    Kn5 l Kt Et, Dn5 l Et, Cs5 l Kt Et, Ds5 l Et,
    fun F kclk coef A a ha r hm σ hin hsh hbl hv hc => by
      obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
      have hm' : mode = .sym := hm
      subst hm'
      exact swnRun x hx l Kt Et tp htp F kclk coef A a ha ha' Cs carriers translation hcall σ hin hsh hbl hv hc⟩

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
