import Proof.Wire_3_5.Primitive.SeedFix.ThrTB6

/-! # THRTAIL T-B, part 7: the THR writer's run at a call

**`thr_run`**: at every THR call of the gate, the THR writer `thrM` runs from `frame thrCallW` to the THR tape within
`128·K²·Y^E·Y^E`, `Y = 2^{m_T(P)} + 1` (`shell_runH4` with every hypothesis discharged: the data side (part 4), the
dimension's `DimOK` at the fill `K_n(n+1)^{D_n}` (T-A's `dimOK`, `need_le`), the scrub capacity (part 5), the unit's
`UnitOK` from THRU4's `U.ok` at `cap = need(meas) + C_L·Y`, the budget (part 1); the output through
`ThrTail.thr_loop_tape` at `C_L·Y ≥ thrTOT`, part 3).

Paper quantity of the main type: the THR tape `thrTape` (P3:3011-3016) written within `2^{O(m_T)}` steps. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.RepairOrdinary

section Writer
variable (l : Literals) (F : GateFree l) (fe D0 C0 kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  (S : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
  (U : ThrUnit.ThrUnitSpec4 l F)

/-- **The THR writer's run at a call.** -/
theorem thr_run (hfe : F.filterErrDeg = fe) (hSD : S.Dc3 ≤ D0) (hSn : S.Dn ≤ D0) (hSC : S.Cc3 ≤ C0) (hSK : S.Kn ≤ C0)
    (hUd : U.deg4 ≤ D0) (hUc : U.cf4 ≤ C0) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    WriterIfaceJ.WriterRun (thrM l F fe D0 C0 kclk coef A a ha S U)
      (128 * (kTB l F fe D0 C0 * kTB l F fe D0 C0 *
        ((2 ^ (dimT l F fe D0).mT ((callInputs l F kclk coef A a ha).starParams n hs) + 1) ^ eT l D0 *
          (2 ^ (dimT l F fe D0).mT ((callInputs l F kclk coef A a ha).starParams n hs) + 1) ^ eT l D0)))
      (ShellT.shellInX4 U.x (dSh D0) (dT2 l D0) (ThrDimB.DnG l) 1 S.x3)
      (ShellT.shellOutX4 U.x (dSh D0) (dT2 l D0) (ThrDimB.DnG l) 1 S.x3)
      (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
      (WriterIface.thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) := by
  -- the unit's constants
  have hU := hUd
  unfold ThrUnit.ThrUnitSpec4.deg4 at hU
  have hUc' := hUc
  unfold ThrUnit.ThrUnitSpec4.cf4 at hUc'
  have hDn : U.Dn ≤ D0 := by omega
  have hDu : U.Du ≤ D0 := by omega
  have hDm : U.Dm ≤ D0 := by omega
  have hKm : U.Km ≤ D0 := by omega
  have hKn : U.Kn ≤ C0 := by omega
  have hKu : U.Ku ≤ C0 := by omega
  -- the dimension
  obtain ⟨m, hmd⟩ : ∃ x, x = (dimT l F fe D0).mT ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  have hge := dim_ge l F kclk coef A a ha hs (kLT l fe D0) (kFT D0)
  have hmeas := meas_le_dim l F kclk coef A a ha ha' Cs carriers translation hcall hs U fe D0 hKm hDm
  have htot := tot_le_dim l F kclk coef A a ha ha' Cs carriers translation hcall hs fe D0 hfe
  have hwm := w_le_dim l F kclk coef A a ha ha' Cs carriers translation hcall hs fe D0
  rw [← hmd] at hge hmeas htot hwm ⊢
  obtain ⟨Y, hY⟩ : ∃ x, x = 2 ^ m + 1 := ⟨_, rfl⟩
  rw [← hY]
  have hn2 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := FinalPass.SymFr.n2_le_L n
  have hLm : 2 ^ Nat.clog 2 (n + 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnY : n + 1 ≤ Y := by omega
  have hwY : (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation).length ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hmY : U.meas kclk coef A a ha n hs a' ha' Cs carriers translation ≤ D0 * Y :=
    hmeas.trans (Nat.mul_le_mul_left _ (by omega))
  -- the loop's units and the scrub capacity
  have hb : UnaryCalc.value 1 (cLT l F) (2 ^ m) = cLT l F * Y := by unfold UnaryCalc.value; rw [pow_one, hY]
  obtain ⟨fc, fn⟩ := unit_fits Y D0 C0 (cLT l F) (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation)
    U.Kn U.Dn U.Ku U.Du U.need U.nU hY1 hmY hKn hDn hKu hDu U.need_le U.nU_le
  have hR : UnaryCalc.value (dSh D0) (cSh D0 C0 (cLT l F)) (2 ^ m) = cSh D0 C0 (cLT l F) * Y ^ dSh D0 := by
    unfold UnaryCalc.value; rw [hY]
  have hboot := boot_le (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) n Y hwY hnY
  have hYd : Y ≤ Y ^ dSh D0 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ dSh D0 := Nat.pow_le_pow_right hY1 (by unfold dSh; nlinarith)
  have hcS : 200 ≤ cSh D0 C0 (cLT l F) := by unfold cSh; omega
  have hboot' : ShellD.bootCost (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) n 0 0 ≤
      UnaryCalc.value (dSh D0) (cSh D0 C0 (cLT l F)) (2 ^ m) := by
    rw [hR]
    have := Nat.mul_le_mul hcS hYd
    omega
  -- the request word
  have hw : ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation =
      Data.reqW ((callInputs l F kclk coef A a ha).starParams n hs).n true
        (ReqBridge.thrCodes (n := ((callInputs l F kclk coef A a ha).starParams n hs).n) Cs)
        (carriers.map Stars.Carrier.code)
        (RepairRepresentation.natListWord translation ++
          ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs) :=
    (ReqBridge.reqW_thrReq ha' Cs carriers translation _).symm
  -- the dimension stage's run
  have hDim := (dimT l F fe D0).dimOK U.x (dSh D0) (dT2 l D0) (ThrDimB.DnG l) 1
    ((callInputs l F kclk coef A a ha).starParams n hs) (PrimT.GeoPack.starParams_r l F kclk coef A a ha n hs) _ _
    (hw.trans (ShellD.reqW_natWord _ _ _ _ _)) (UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn n)
    ((dimT l F fe D0).need_le _ (PrimT.GeoPack.starParams_r l F kclk coef A a ha n hs))
  rw [← hmd] at hDim
  -- the budget
  have hE1 : dSh D0 + 1 ≤ eT l D0 := by unfold eT; omega
  have hE2 : dT2 l D0 + 1 ≤ eT l D0 := by unfold eT; omega
  have hE3 : ThrDimB.DnG l + 1 ≤ eT l D0 := by unfold eT; omega
  have hE4 : 1 + 1 ≤ eT l D0 := by unfold eT; omega
  have hcc := cc_le l F fe D0 C0 kclk coef A a ha S hSD hSC ha' Cs carriers translation hcall Y hnY
  have hc2 := c2_le' l F fe D0 ((callInputs l F kclk coef A a ha).starParams n hs) Y hnY
  have hc2' : (dimT l F fe D0).c2 (UnaryCalc.value (ThrDimB.DnG l) (dimT l F fe D0).Kn n)
      ((callInputs l F kclk coef A a ha).starParams n hs) ≤ kTB l F fe D0 C0 * Y ^ eT l D0 := by
    refine hc2.trans (Nat.mul_le_mul (by unfold kTB; omega) (Nat.pow_le_pow_right hY1 (by unfold eT; omega)))
  have hnU : U.nU (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation +
      (U.need (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation) + cLT l F * Y)) ≤
      kTB l F fe D0 C0 * Y ^ eT l D0 := by
    have a1 : cSh D0 C0 (cLT l F) * Y ^ dSh D0 ≤ kTB l F fe D0 C0 * Y ^ eT l D0 :=
      Nat.mul_le_mul (by unfold kTB; omega) (Nat.pow_le_pow_right hY1 (by omega))
    omega
  have hK : kShell (dSh D0) (cSh D0 C0 (cLT l F)) (dT2 l D0) (cT2 l F C0) (ThrDimB.DnG l) (dimT l F fe D0).Kn 1
      (cLT l F) ≤ kTB l F fe D0 C0 := by unfold kTB; omega
  have hB := costG_le (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation) n (dSh D0)
    (cSh D0 C0 (cLT l F)) (dT2 l D0) (cT2 l F C0) _ (ThrDimB.DnG l) (dimT l F fe D0).Kn _ m 1 (cLT l F) _ Y (eT l D0)
    (kTB l F fe D0 C0) (by omega) hnY hwY hE1 hE2 hE3 hE4 hK hcc hc2' hnU
  -- the unit's runs
  have hdec : ∀ j < UnaryCalc.value 1 (cLT l F) (2 ^ m), ∀ out : List Bool,
      PrimThrW.Shell.UnitOK (U.need (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation) + cLT l F * Y) U.x U.U
        (U.nU (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation +
          (U.need (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation) + cLT l F * Y)))
        (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
        (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
          (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ++
          ThrData.thrCounts Cs carriers))
        (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
          (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) j out := by
    intro j hj out
    rw [hb] at hj
    exact U.ok kclk coef A a ha n hs a' ha' Cs carriers translation hcall out j _ (by omega)
  have hrun := ShellT.shell_runH4 S U.x U.U (dSh D0) (cSh D0 C0 (cLT l F)) (dT2 l D0) (cT2 l F C0) (ThrDimB.DnG l)
    (dimT l F fe D0).Kn 1 (cLT l F) (dimT l F fe D0).M2 _ m
    (U.need (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation) + cLT l F * Y)
    (U.nU (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation +
      (U.need (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation) + cLT l F * Y)))
    _ ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers _ _
    (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
      (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) hw
    (data_ok l F kclk coef A a ha ha' Cs carriers translation hcall D0 C0)
    (data_cu l F kclk coef A a ha ha' Cs carriers translation hcall hs D0 C0) hcall.2.2.1
    (data_need S l F D0 C0 n hSn hSK) hDim (by rw [hR]; omega) (by rw [hR]; omega) hboot' hdec hB
  have htot' : ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers ≤ UnaryCalc.value 1 (cLT l F) (2 ^ m) := by
    rw [hb]
    have : cLT l F * 2 ^ m ≤ cLT l F * Y := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [ThrTail.thr_loop_tape l F kclk coef A a ha hs Cs carriers translation _ htot'] at hrun
  exact hrun

end Writer

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
