import Lean
import Proof.Wire_3_5.Primitive.Writers.SBTypes2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SBIdent
import Proof.Wire_3_5.Primitive.Writers.SBLay
import Proof.Wire_3_5.Primitive.Writers.SBRun
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SBInstBase


noncomputable section
set_option maxRecDepth 4096


/-! # SB, part (6): S4's words `4 … 7` as a writer (`S4WordsMBJ l`)

* `clearAllCost_eq`, `A0`, `CsOf`, `DsOf`, **`sb_contract`** (the writer's run at the capacity `Kc F·(N+1)^{Dk fe}`,
  from the arithmetic targets with explicit constants);
* **`sbWriter`**: `Finish.S4WordsMBJ l` from `SBIdentStmts l`, `SBOutsStmt l` (the identifications and `sb_outs`),
  `SBCostStmt l`, `SBFieldCostStmt l`, `SBCapStmt l` (the arithmetic targets).

Paper quantity of the main type: S4's words `4 … 7` at a star call (`s4Core2`: the field words, the walk's threshold,
`s4Small2`; P3:3170-3181) within `prim:runtime` (P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Out.Car NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums NearCubicWires.WireExponent3_5.PrimAsm.SBTypes

/-- **The writer's run** at the capacity `Kc F·(N+1)^{Dk fe}`, from the targets with explicit constants. -/
theorem sb_contract (l : Literals) (hI : SBIdent.SBIdentStmts l) (hO : SBOutsStmt l) (Cc E : ℕ)
    (hC : ∀ (F : GateFree l) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ),
      sbNeed l F.cr F.filterErrDeg P m wl c0 c1 nc ≤ cap →
        p1Cost cap wl P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg F.cr c0 c1 nc ≤
          Cc * cap ^ E)
    (Cf Ef : ℕ) (hF : ∀ (F : GateFree l) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ),
      sbNeed l F.cr F.filterErrDeg P m wl c0 c1 nc ≤ cap →
        SBField.fieldCost cap (ellOf P.n) ((SBField.eraseL FsB).map fun i => i.val) ≤ Cf * cap ^ Ef)
    (Kc : GateFree l → ℕ) (Dk : ℕ → ℕ)
    (hK : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
      (hs : (callInputs l F kclk coef A a ha).StarAt r.1.n),
      sbNeed l F.cr F.filterErrDeg ((callInputs l F kclk coef A a ha).starParams r.1.n hs) r.1.mode
          (fpIn l F kclk coef A a ha r).length (carCnt r.1.carriers 0) (carCnt r.1.carriers 1) r.1.carriers.length ≤
        Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg)
    (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (σ : WState nsB NRB)
    (hin : σ.st sInB = frame (fpIn l F kclk coef A a ha r)) (hsh : ∀ i, σ.sh i = 0)
    (hbl : ∀ i, i ≠ sInB → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hc : σ.cell = false) :
    ∃ (τ : WState nsB NRB) (n : ℕ),
      n ≤ CsOf Cc E Cf Ef (Kc F) * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsOf E Ef (Dk F.filterErrDeg) ∧
      Step (sbMach l F).2 n
        (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).H
        (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).A
        (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).H
        (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).A ∧
      (∀ k : Fin 4, τ.st (sOutB k) = Seams.frontWordsW2 l F kclk coef A a ha Finish.Sw0 r (Finish.s4SlotB k)) ∧
      τ.st sInB = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ sInB → (∀ k, i ≠ sOutB k) →
        (τ.st i).length ≤ CsOf Cc E Cf Ef (Kc F) * ((fpIn l F kclk coef A a ha r).length + 1) ^
          DsOf E Ef (Dk F.filterErrDeg)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  obtain ⟨K, hKd⟩ : ∃ K, K = Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg := ⟨_, rfl⟩
  have hN : sbNeed l F.cr F.filterErrDeg (Pof r) r.1.mode (fpIn l F kclk coef A a ha r).length
      (carCnt r.1.carriers 0) (carCnt r.1.carriers 1) r.1.carriers.length ≤ K := hKd ▸ hK F kclk coef A a ha r _
  have hK1 : 1 ≤ K := by
    have := (need_parts l F.cr F.filterErrDeg (Pof r) r.1.mode _ _ _ _ K hN).2.2.2.2.2.2.2.2.1
    clear * - this; omega
  obtain ⟨τ, n, hn, hstep, hexit, hkeep, hres, hτs, hτv⟩ := sb_run l hI.starR F kclk coef A a ha r σ hin hsh hbl hv hc K hN
  obtain ⟨hpow, hmul⟩ := cap_pow Cc E Cf Ef (Kc F) (fpIn l F kclk coef A a ha r).length (Dk F.filterErrDeg) K hKd hK1
  have hp1 := hC F (Pof r) r.1.mode _ _ _ _ K hN
  have hf1 := hF F (Pof r) r.1.mode _ _ _ _ K hN
  have k2 : K ^ 2 ≤ K ^ (E + Ef + 2) := Nat.pow_le_pow_right hK1 (by omega)
  have kE : K ^ E ≤ K ^ (E + Ef + 2) := Nat.pow_le_pow_right hK1 (by omega)
  have kF : K ^ Ef ≤ K ^ (E + Ef + 2) := Nat.pow_le_pow_right hK1 (by omega)
  have k1 : K ≤ K ^ (E + Ef + 2) := by
    have := Nat.pow_le_pow_right hK1 (show 1 ≤ E + Ef + 2 by omega); rwa [pow_one] at this
  have m0 : A0 * K ^ 2 ≤ A0 * K ^ (E + Ef + 2) := Nat.mul_le_mul_left _ k2
  have mC : Cc * K ^ E ≤ Cc * K ^ (E + Ef + 2) := Nat.mul_le_mul_left _ kE
  have mF : Cf * K ^ Ef ≤ Cf * K ^ (E + Ef + 2) := Nat.mul_le_mul_left _ kF
  have hsplit : (A0 + Cc + Cf + 1000) * K ^ (E + Ef + 2) =
      A0 * K ^ (E + Ef + 2) + Cc * K ^ (E + Ef + 2) + Cf * K ^ (E + Ef + 2) + 1000 * K ^ (E + Ef + 2) := by ring
  have hcl := clearAllCost_eq K 112
  refine ⟨τ, n, ?_, hKd ▸ hstep, ?_, hkeep, ?_, hτs, hτv⟩
  · refine le_trans ?_ hmul
    unfold sbCost at hn
    rw [hsplit]
    have hA0 : (57600 * (DtC + 1) + 10 ^ 6) * K ^ 2 = A0 * K ^ 2 := rfl
    rw [hA0, List.length_finRange, show NRB = 112 from rfl, hcl] at hn
    clear * - hn hp1 hf1 m0 mC mF k1 hK1
    omega
  · intro k
    exact (hexit k).trans (hO hI F kclk coef A a ha r _ k)
  · intro i hi hk
    exact ((hres i hi hk).trans k1).trans hpow

/-- **SB: S4's words `4 … 7` as a writer** (the split's assembly). -/
noncomputable def sbWriter (l : Literals) (hI : SBIdent.SBIdentStmts l) (hO : SBOutsStmt l) (hC : SBCostStmt l)
    (hF : SBFieldCostStmt l) (hK : SBCapStmt l) : Finish.S4WordsMBJ l where
  ns := nsB
  nr := NRB
  s := fun F => (sbMach l F).1
  M := fun F => (sbMach l F).2
  sIn := sInB
  sOut := sOutB
  out_ne := sOutB_ne
  Kc := Classical.choose hK
  Dk := Classical.choose (Classical.choose_spec hK)
  Cs := fun F => CsOf (Classical.choose hC) (Classical.choose (Classical.choose_spec hC)) (Classical.choose hF)
    (Classical.choose (Classical.choose_spec hF)) (Classical.choose hK F)
  Ds := fun fe => DsOf (Classical.choose (Classical.choose_spec hC)) (Classical.choose (Classical.choose_spec hF))
    (Classical.choose (Classical.choose_spec hK) fe)
  run := fun F kclk coef A a ha r σ hin hsh hbl hv hc =>
    sb_contract l hI hO _ _ (Classical.choose_spec (Classical.choose_spec hC)) _ _
      (Classical.choose_spec (Classical.choose_spec hF)) _ _ (Classical.choose_spec (Classical.choose_spec hK))
      F kclk coef A a ha r σ hin hsh hbl hv hc

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
