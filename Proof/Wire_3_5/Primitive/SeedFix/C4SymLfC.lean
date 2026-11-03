import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfB
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.C4BudF
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNE
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SymLeafC4, part 3: the SYM part of C4Leaf

P3:3105-3115 (the seed-fixing budget `c₄·seedClasses E₄`: `E₄` before `F`, `c₄` after), P3:3011-3016, 3034-3038 (the
SYM stage), #148 (the floors `CD ≥ CD_s`, `cpsi ≥ 1`), #156/#159 (contract v7, `Atable ≥ Dp + 1`): from the builder
of the free numbers (`SymBuild7`), the C3 request writers (`C3ReqLeaf3` at `c_N = K3`, `D_N = D3`) and C1b's
eval-unchanged lemma (`PadEval`): after `fe`, `E₄ = emax E_W (Atable ≥ Dp+1, cpsi ≥ 1)` and `CD₄ = max(CD_s, CD_W, 1)`;
for every admissible `F`, the capacity constant `C_c` (`sym_fits2`, `sym_bigS2`), `c₄` (`sym_steps_gen`), and at every
call family the branched stage `padStage (symStageU3 …)` at the layout `symLay` (the C3 writer of the family), running
at every SYM call: with rows `sym_plain_run`, degenerate `sym_deg_run` (pad `padCost E ≤ K_P·2^{⌊n/8⌋}`).

* `SymBuild7`, `symSB`, `symFloor`, `symLay`, `pad_le_cap`, **`symLeafC4_of`**, **`symLeafC4`**.

Paper quantity of the main type: the SYM part of the C4 leaf (the fixed seeds within `c₄·seedClasses E₄`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters

/-- **The builder of the free numbers**, v7: after `fe`, the floor `CD_s` and the constants `K3, D3, Kp, Dp`;
for every admissible `F`, the contract. -/
def SymBuild7 (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) : Type :=
  ∀ fe : ℕ, Σ CDs K3 D3 Kp Dp : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → CDs ≤ F.CD → 1 ≤ F.E.cpsi →
    C4SymW.SymFreeOk7 l F wa K3 D3 Kp Dp

/-- The SYM numbers' base constants at the gate (`sym_needs`' equations by `rfl`). -/
noncomputable def symSB (l : Literals) (F : GateFree l) (Cw Dw Cnw Dnw : ℕ) : SB where
  Cw := Cw
  Dw := Dw
  Cnw := Cnw
  Dnw := Dnw
  Csy := 0
  Dsy := 0
  Cn := 0
  Dn := 0
  Cb := 0
  Db := 0
  Qn := 0
  Qd := 0
  Qb := 0
  Qe := 0
  Kf := 0
  Df := 0
  Kp := 0
  Dp := 0
  Z := CallIndexR.capZR l
  Zm := 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32
  Csp := gateCsp l
  J := SymSizes.schedJ l
  cX := SymSizes.cXg l
  KLam := 0
  capK := CallIndexR.capK F.cr
  cr := F.cr
  fe := F.filterErrDeg
  cM := CapNum.cMain (gateCap l) .sym

/-- **The SYM part of C4Leaf** from the builder (v7), the C3 request writers and the eval-unchanged lemma, at the
call words' and `needW`'s polynomial bounds. -/
noncomputable def symLeafC4_of (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) (Cw Dw Cnw Dnw : ℕ)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ Cw * (n + 1) ^ Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw)
    (Bld : SymBuild7 l wa) (W3 : C3ReqIface3.C3ReqLeaf3 l) (he : PadEval) : C4K.SymLeafC4 l := by
  intro fe
  obtain ⟨CDs, K3, D3, Kp, Dp, mk⟩ := Bld fe
  obtain ⟨EW, CDW, mkW⟩ := W3 K3 D3 fe
  refine ⟨C4K.emax EW (symFloor Dp), max (max CDs CDW) 1, fun F hfe hE hCD => ?_⟩
  have hEW : ClassLE EW F.E := C4K.classLE_trans (C4K.le_emax_left EW _) hE
  have hcp : 1 ≤ F.E.cpsi := (C4K.le_emax_right EW (symFloor Dp)).cpsi.trans hE.cpsi
  have hCDs : CDs ≤ F.CD := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCD
  have hCDW : CDW ≤ F.CD := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCD
  have hCD1 : 1 ≤ F.CD := le_trans (le_max_right _ _) hCD
  have S := mk F hfe hCDs hcp
  obtain ⟨cW, W⟩ := mkW F hfe hEW hCDW
  have hWL : ∀ n, PrimT.C4GateSym.needW n ≤ UnaryCalc.value (Dnw + 16) (Cnw + 1) n := fun n => by
    have h1 := hnw n
    have h2 : (n + 1) ^ Dnw ≤ (n + 1) ^ (Dnw + 16) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : Cnw * (n + 1) ^ Dnw ≤ (Cnw + 1) * (n + 1) ^ (Dnw + 16) :=
      Nat.mul_le_mul (Nat.le_succ _) h2
    show _ ≤ (Cnw + 1) * (n + 1) ^ (Dnw + 16)
    omega
  have hfit := C4SymN.sym_fits2 l F S.Fp S.ok_le S.val_le S.rho_le (symSB l F Cw Dw Cnw Dnw) hwb hnw rfl rfl rfl rfl
    rfl rfl rfl rfl rfl
  have hbigS := C4SymN.sym_bigS2 l F S.Fp S.ok_le S.val_le S.rho_le (symSB l F Cw Dw Cnw Dnw) hwb hnw rfl rfl rfl rfl
    rfl rfl rfl rfl rfl
  have hEc : EW.cpsi ≤ (C4K.emax EW (symFloor Dp)).cpsi := (C4K.le_emax_left EW (symFloor Dp)).cpsi
  have hEa : EW.Apre ≤ (C4K.emax EW (symFloor Dp)).Apre := (C4K.le_emax_left EW (symFloor Dp)).Apre
  have hAt : Dp + 1 ≤ (C4K.emax EW (symFloor Dp)).Atable := (C4K.le_emax_right EW (symFloor Dp)).Atable
  have hsteps := C4Bud.sym_steps_gen l F Kp Dp S.Fp (Classical.choose S.cost_le) (Classical.choose_spec S.cost_le)
    (Classical.choose S.rho_le) (Classical.choose (Classical.choose_spec S.rho_le))
    (Classical.choose_spec (Classical.choose_spec S.rho_le)) S.pad_le (symSB l F Cw Dw Cnw Dnw) hwb hnw rfl rfl rfl
    rfl rfl rfl rfl rfl rfl (Dnw + 16) (Cnw + 1) (Cnw + 1) (max (Classical.choose hfit) (Classical.choose hbigS)) hWL
    EW (C4K.emax EW (symFloor Dp)) cW hEc hEa hAt
    ((8 * C4Pad.W1.length + 28) * 2 ^ max (Classical.choose hfit) (Classical.choose hbigS))
  refine ⟨Classical.choose hsteps, fun kclk coef A a ha =>
    ⟨C4Pad.padStage (C4SymW.symStageU3 (symLay wa (W kclk coef A a ha).sym Dnw) (Cnw + 1) (Cnw + 1)
      (max (Classical.choose hfit) (Classical.choose hbigS)) S.Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l)
      (gateCap l) wa (symLay_T wa _ Dnw) (le_refl 31)), fun n a' ha' Cs carriers translation hcall hs => ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, fcnt, -, -, -, -, -, -, hkq⟩ := Classical.choose_spec hfit
    (max (Classical.choose hfit) (Classical.choose hbigS)) (le_max_left _ _) kclk coef A a ha n a' ha' Cs carriers
    translation hcall hs
  have hbig := Classical.choose_spec hbigS (max (Classical.choose hfit) (Classical.choose hbigS)) (le_max_right _ _)
    kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  have hst := Classical.choose_spec hsteps kclk coef A a ha n a' ha' Cs carriers translation hcall hs hkq
    (symLay wa (W kclk coef A a ha).sym Dnw) rfl
  by_cases hR0 : carriers.length + 2 * a' = 0
  · have hNT := C4SymL.symNT_link (callInputs l F kclk coef A a ha) Cs carriers hs ha' rfl rfl
    have fcnt' : PrimAsm.Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers *
        2 ^ C4Set.wOf (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
          (SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers) + 1 ≤
        2 ^ C4Cap.capExp2 (max (Classical.choose hfit) (Classical.choose hbigS)) n := by
      rw [← hNT]; exact fcnt
    have hE0 : PrimAsm.Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers *
        (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 ≤
        2 ^ C4Cap.capExp2 (max (Classical.choose hfit) (Classical.choose hbigS)) n := by
      have h2 : (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 ≤
          2 ^ C4Set.wOf (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
            (SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers) := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by unfold C4Set.wOf; omega)
      have h3 := Nat.mul_le_mul_left (PrimAsm.Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) h2
      omega
    exact sym_deg_run he l F wa EW cW K3 D3 kclk coef A a ha (W kclk coef A a ha) (symLay wa (W kclk coef A a ha).sym Dnw)
      rfl (by show 16 ≤ Dnw + 16; omega) (symLay_T wa _ Dnw) (le_refl 31) (Cnw + 1)
      (max (Classical.choose hfit) (Classical.choose hbigS)) S.Fp ha' Cs carriers translation hcall hs hR0 (hWL n) _ _ _ _
      (S.side_pad kclk coef A a ha n a' ha' Cs carriers translation hcall hs hR0)
      (S.c3_le hCD1 kclk coef A a ha n a' ha' Cs carriers translation hcall hs) _ hbig _
      (fun Fm hc hb => hst Fm hc hb _ (pad_le_cap _ _ n hE0))
  · exact sym_plain_run l F wa EW cW K3 D3 kclk coef A a ha (W kclk coef A a ha) (symLay wa (W kclk coef A a ha).sym Dnw)
      rfl (by show 16 ≤ Dnw + 16; omega) (symLay_T wa _ Dnw) (le_refl 31) (Cnw + 1)
      (max (Classical.choose hfit) (Classical.choose hbigS)) S.Fp ha' Cs carriers translation hcall hs (by omega) (hWL n)
      _ _ _ _ (S.side kclk coef A a ha n a' ha' Cs carriers translation hcall hs (by omega))
      (S.c3_le hCD1 kclk coef A a ha n a' ha' Cs carriers translation hcall hs) _ hbig _
      (fun Fm hc hb => hst Fm hc hb 0 (Nat.zero_le _))

/-- **The SYM part of C4Leaf**, at the call words' and `needW`'s polynomial bounds (`wordBound_poly`, `needW_pb`). -/
noncomputable def symLeafC4 (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) (Bld : SymBuild7 l wa)
    (W3 : C3ReqIface3.C3ReqLeaf3 l) (he : PadEval) : C4K.SymLeafC4 l :=
  symLeafC4_of l wa (Classical.choose CallSize.wordBound_poly)
    (Classical.choose (Classical.choose_spec CallSize.wordBound_poly))
    (Classical.choose PrimT.C4GateSym.needW_pb) (Classical.choose (Classical.choose_spec PrimT.C4GateSym.needW_pb))
    (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2
    (Classical.choose_spec (Classical.choose_spec PrimT.C4GateSym.needW_pb)).2 Bld W3 he

end NearCubicWires.WireExponent3_5.PrimT.C4SymLf

end
