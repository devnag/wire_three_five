import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrLf1
import Proof.Wire_3_5.Primitive.Writers.C3W3Leaf
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.HashLeaf
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrB7
import Proof.Wire_3_5.Primitive.Writers.ThrBud2
import Proof.Wire_3_5.Primitive.Writers.ThrCap3
import Proof.Wire_3_5.Primitive.Writers.ThrK7
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Primitive.SeedFix.TS4L
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 9 part 2: `ThrLeafC4` (the THR part of C4Leaf)

The THR twin of the `symLeafC4_of`/`symLeafC4` (C4SymLfC): P3:3105-3115 (the seed-fixing budget
`c₄·seedClasses E₄`: `E₄` before `F`, `c₄` after), P3:3011-3016, 3034-3038 (the THR stage), #148 (the floors),
#162 (the strip): from the THR builder (`ThrFreeOkB7`, `ThrSide.thrFreeOk`), PA's C3 request writers (`C3ReqLeaf3`
at `c_N = K3`, `D_N = D3`) and the v4 data stage (`stage4At`, uniform constants): after `fe`,
`E₄ = emax E_W (Atable ≥ Dp+1, cpsi ≥ 1)` and `CD₄ = max(CD_t, CD_W, 1)`; for every admissible `F`, the capacity
constant `C_c` (`thr_fits2`), `c₄` (`thr_steps_gen`), and at every call family the THR stage `thrStageU3` at the
layout `symLay` with the family's C3 writer through the strip (`ThrStrip.thrC3`), running at every THR call
(`thr_plain_run`).
* **`thrLeafC4_of`**, **`thrLeafC4`** : `C4K.ThrLeafC4 l`.

Paper quantity of the main type: the THR part of the C4 leaf (the fixed seeds within `c₄·seedClasses E₄`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- `needW` below the stage's unary numbers `(C_nw + 1)(n+1)^{D₀+16}`. -/
theorem thr_hWL (l : Literals) (Cnw Dnw : ℕ) (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) (n : ℕ) :
    PrimT.C4GateSym.needW n ≤ UnaryCalc.value ((Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l) + 16) (Cnw + 1) n := by
  have h1 := hnw n
  have h2 : (n + 1) ^ Dnw ≤ (n + 1) ^ ((Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l) + 16) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : Cnw * (n + 1) ^ Dnw ≤ (Cnw + 1) * (n + 1) ^ ((Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l) + 16) := Nat.mul_le_mul (Nat.le_succ _) h2
  show _ ≤ (Cnw + 1) * (n + 1) ^ ((Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l) + 16)
  omega

/-- **The THR part of C4Leaf** from the THR builder (v7), PA's C3 request writers and the v4 data stage, at the call
words' and `needW`'s polynomial bounds. -/
noncomputable def thrLeafC4_of (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) (Cw Dw Cnw Dnw : ℕ)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ Cw * (n + 1) ^ Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw)
    (Bld : ThrFam.ThrFreeOkB7 l wa) (W3 : C3ReqIface3.C3ReqLeaf3 l) : PrimT.C4K.ThrLeafC4 l := by
  intro fe
  obtain ⟨CDt, K3, D3, Kp, Dp, mk⟩ := Bld fe
  obtain ⟨EW, CDW, mkW⟩ := W3 K3 D3 fe
  refine ⟨(PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)), max (max CDt CDW) 1, fun F hfe hE hCD => ?_⟩
  have hEW : ClassLE EW F.E := PrimT.C4K.classLE_trans (PrimT.C4K.le_emax_left EW _) hE
  have hcp : 1 ≤ F.E.cpsi := (PrimT.C4K.le_emax_right EW (PrimT.C4SymLf.symFloor Dp)).cpsi.trans hE.cpsi
  have hCDt : CDt ≤ F.CD := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD
  have hCDW : CDW ≤ F.CD := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD
  have hCD1 : 1 ≤ F.CD := le_trans (le_max_right _ _) hCD
  have S := mk F hfe hCDt hcp
  obtain ⟨cW, W⟩ := mkW F hfe hEW hCDW
  have hfit := ThrCap.thr_fits2 l F S.Fp S.ok_le S.val_le S.rho_le Cw Dw Cnw Dnw hwb hnw
  have hEc : EW.cpsi ≤ (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)).cpsi := (PrimT.C4K.le_emax_left EW (PrimT.C4SymLf.symFloor Dp)).cpsi
  have hEa : EW.Apre ≤ (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)).Apre := (PrimT.C4K.le_emax_left EW (PrimT.C4SymLf.symFloor Dp)).Apre
  have hAt : Dp + 1 ≤ (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)).Atable := (PrimT.C4K.le_emax_right EW (PrimT.C4SymLf.symFloor Dp)).Atable
  have hsteps := ThrBud.thr_steps_gen l F Kp Dp S.Fp (Classical.choose S.cost_le) (Classical.choose_spec S.cost_le)
    S.pad_le (PrimT.TS4.stage4At l F) (PrimT.TS4.CcG l F.cr) (PrimT.TS4.DcG l) (fun _ _ _ _ _ => ⟨le_rfl, le_rfl⟩)
    ((Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l) + 16) (Cnw + 1) (Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) + PrimT.TS4.NCoef l F.cr) (Classical.choose hfit) (thr_hWL l Cnw Dnw hnw) EW (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp))
    cW hEc hEa hAt
  refine ⟨Classical.choose hsteps, fun kclk coef A a ha =>
    ⟨ThrSet.thrStageU3 (PrimT.C4SymLf.symLay wa (ThrStrip.thrC3 (W kclk coef A a ha).thr) (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l)) (Cnw + 1)
      (Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) + PrimT.TS4.NCoef l F.cr) (Classical.choose hfit) (PrimT.TS4.stage4At l F kclk coef A a ha).x3
      (PrimT.TS4.stage4At l F kclk coef A a ha).s3 (PrimT.TS4.stage4At l F kclk coef A a ha).M3 S.Fp F.cr
      F.filterErrDeg wa (PrimT.C4SymLf.symLay_T wa _ _), fun n a' ha' Cs carriers translation hcall hs => ?_⟩⟩
  have hfc := Classical.choose_spec hfit (Classical.choose hfit) le_rfl kclk coef A a ha n a' ha' Cs carriers translation
    hcall hs
  have hst := Classical.choose_spec hsteps kclk coef A a ha n a' ha' Cs carriers translation hcall hs hfc
    (PrimT.C4SymLf.symLay wa (ThrStrip.thrC3 (W kclk coef A a ha).thr) (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l)) rfl
  obtain ⟨hWL', hLW, hcu, hneed⟩ := thr_data_W l F kclk coef A a ha ha' Cs carriers translation hcall hs Cnw Dnw (hnw n)
    (PrimT.TS4.NCoef l F.cr) (PrimT.TS4.NDeg l) ((PrimT.TS4.stage4At l F kclk coef A a ha).need n)
    ((PrimT.TS4.stage4At l F kclk coef A a ha).need_le n)
  exact thr_plain_run l F wa EW cW K3 D3 kclk coef A a ha (W kclk coef A a ha)
    (PrimT.C4SymLf.symLay wa (ThrStrip.thrC3 (W kclk coef A a ha).thr) (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l)) rfl
    (by show 16 ≤ (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + PrimT.TS4.NDeg l) + 16; omega) (PrimT.C4SymLf.symLay_T wa _ _) (le_refl 31) (Cnw + 1) (Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) + PrimT.TS4.NCoef l F.cr)
    (Classical.choose hfit) S.Fp (PrimT.TS4.stage4At l F kclk coef A a ha) ha' Cs carriers translation hcall hs hWL' hLW
    hcu hneed _ _ _ _ (S.side kclk coef A a ha n a' ha' Cs carriers translation hcall hs)
    (S.c3_le hCD1 kclk coef A a ha n a' ha' Cs carriers translation hcall hs)
    (S.strip kclk coef A a ha n a' ha' Cs carriers translation hcall hs) hfc _ (fun Fm hc hb s => hst Fm hc hb s)

/-- **The THR part of C4Leaf**, at the call words' and `needW`'s polynomial bounds, from the THR builder
`ThrSide.thrFreeOk` and PA's C3 request writers `C3Leaf.c3ReqLeaf3`. -/
noncomputable def thrLeafC4 (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) : PrimT.C4K.ThrLeafC4 l :=
  thrLeafC4_of l wa (Classical.choose CallSize.wordBound_poly)
    (Classical.choose (Classical.choose_spec CallSize.wordBound_poly))
    (Classical.choose PrimT.C4GateSym.needW_pb) (Classical.choose (Classical.choose_spec PrimT.C4GateSym.needW_pb))
    (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2
    (Classical.choose_spec (Classical.choose_spec PrimT.C4GateSym.needW_pb)).2 (ThrSide.thrFreeOk l wa)
    (C3Leaf.c3ReqLeaf3 l)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrLf

end
