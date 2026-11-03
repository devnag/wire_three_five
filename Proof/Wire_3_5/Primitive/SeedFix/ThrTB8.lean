import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB7
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.Primitive.Writers.ThrDimIface
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJ
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB3
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB4
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB6
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.ThrDimC
import Proof.Wire_3_5.UnionMachine.ThrDimG
import Proof.Wire_3_5.UnionMachine.ThrDimN
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB6Base


noncomputable section
set_option maxRecDepth 4096


/-! # T3 THRTAIL T-B, part 8: the THR writer at the class link's order of choice, and THRTAIL's `tail`

**`thrW`**: the THR writer `thrM` as `ThrWriterAtJ l F (EWT l f_e D₀) (cWT l F f_e D₀ C₀)`: the run `thr_run`
lifted by the class link `class_linkT` (the dimension's `m_le`, `C_D ≥ 1`) into `c_W·classBound E_W .preprocessing
n k Ψ` with `c_ψ(E_W) = 2E(2 + K_L + 8K_f)` (P3:3108, 3112-3114). **`thrLeafU4 : ThrLeafOfU4 l`**: the dock (ThrTail0's
order of choice at THRU4: the two uniform families side by side, the floors `envMax E₀ (EWT l f_e D₀)` and
`max CD₀ 1`, the coefficient after `F`). **`tail`**: `∀ l, PreLinkT l → ThrLeafOfU4 l`, `thrClose2`'s open binder.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3011-3016,
3108, 3112-3114). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.Cost

/-- The THR writer's floor envelope (from `(l, f_e, D₀)`): `c_ψ = 2E(2 + K_L + 8K_f)`. -/
noncomputable def EWT (l : Literals) (fe D0 : ℕ) : Envelope :=
  ⟨0, 0, 0, 0, 0, 0, 0, 2 * eT l D0 * (2 + kLT l fe D0 + 8 * kFT D0)⟩

/-- The THR writer's class coefficient (after `F`). -/
noncomputable def cWT (l : Literals) (F : GateFree l) (fe D0 C0 : ℕ) : ℕ :=
  128 * (kTB l F fe D0 C0 * kTB l F fe D0 C0) * 2 ^ (2 * eT l D0)

section Writer
variable (l : Literals) (F : GateFree l) (fe D0 C0 kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  (S : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
  (U : ThrUnit.ThrUnitSpec4 l F)

/-- **The THR writer at a gate** (T-B). -/
noncomputable def thrW (hfe : F.filterErrDeg = fe) (hSD : S.Dc3 ≤ D0) (hSn : S.Dn ≤ D0) (hSC : S.Cc3 ≤ C0)
    (hSK : S.Kn ≤ C0) (hUd : U.deg4 ≤ D0) (hUc : U.cf4 ≤ C0) (hCD : 1 ≤ F.CD) :
    WriterIfaceJ.ThrWriterAtJ l F (EWT l fe D0) (cWT l F fe D0 C0) kclk coef A a ha where
  t := _
  s := _
  M := thrM l F fe D0 C0 kclk coef A a ha S U
  inS := ShellT.shellInX4 U.x (dSh D0) (dT2 l D0) (ThrDimB.DnG l) 1 S.x3
  outS := ShellT.shellOutX4 U.x (dSh D0) (dT2 l D0) (ThrDimB.DnG l) 1 S.x3
  hio := ShellT.shellInX4_ne_out _ _ _ _ _ _
  ready := fun n a' ha' Cs carriers translation hcall hs => by
    refine WritersJoin.writerRun_mono (thr_run l F fe D0 C0 kclk coef A a ha S U hfe hSD hSn hSC hSK hUd hUc ha' Cs
      carriers translation hcall hs) ?_
    have hm := dim_le l F kclk coef A a ha hs (kLT l fe D0) (kFT D0)
    have hL1 := FinalPass.SymFr.one_le_L n
    have hn1 : 1 ≤ n := PrimT.GeoPack.star_n_pos hs
    exact class_linkT (EWT l fe D0) (eT l D0) (kTB l F fe D0 C0) (kLT l fe D0) (kFT D0) F.CD n
      (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
      (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
      _ hL1 hCD hn1 hm le_rfl

end Writer

/-- **The THR writer's leaf from the unit machines v4** (T-B's dock, ThrTail0's order of choice at THRU4). -/
noncomputable def thrLeafU4 (l : Literals) : ThrUnit.ThrLeafOfU4 l := fun SU UU fe =>
  ⟨envMax (FinalPass.Seams.StageU.pair SU UU fe).2.1 (EWT l fe (FinalPass.Seams.StageU.pair SU UU fe).1),
    max (FinalPass.Seams.StageU.pair SU UU fe).2.2.1 1, fun F hF hE hCD =>
    ⟨cWT l F fe (FinalPass.Seams.StageU.pair SU UU fe).1
        ((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
          (le_trans (le_max_left _ _) hCD)).1, fun kclk coef A a ha =>
      WritersJoin.thrMono
        (thrW l F fe (FinalPass.Seams.StageU.pair SU UU fe).1
          ((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
            (le_trans (le_max_left _ _) hCD)).1 kclk coef A a ha
          (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
            (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).1.1
          (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
            (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).1.2
          hF
          (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
            (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2.1)
          (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
            (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2.1)
          (by
            have h := (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2.2
            dsimp only at h
            omega)
          (by
            have h := (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2.2
            dsimp only at h
            omega)
          (le_trans (le_max_right _ _)
            (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2.1)
          (by
            have h := (((FinalPass.Seams.StageU.pair SU UU fe).2.2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
              (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha).2.2
            dsimp only at h
            omega)
          (le_trans (le_max_right _ _) hCD))
        (classLE_envMax_right _ _) le_rfl⟩⟩

/-- **THRTAIL's `tail`**: `thrClose2`'s open binder. -/
noncomputable def tail : ∀ l : Literals, PreLink.PreLinkT l → ThrUnit.ThrLeafOfU4 l := fun l _ => thrLeafU4 l

end NearCubicWires.WireExponent3_5.PrimT.ThrTB

end
