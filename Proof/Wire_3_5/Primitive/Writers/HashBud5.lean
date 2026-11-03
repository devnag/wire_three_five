import Lean
import Proof.Wire_3_5.Primitive.Writers.HashBud2
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2Base
import Proof.Wire_3_5.Primitive.Writers.HashLfV3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashFree
import Proof.Wire_3_5.FinalPass.HashFree2
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashSz2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.HashBud3
import Proof.Wire_3_5.Primitive.Writers.HashBud4
import Proof.Wire_3_5.Primitive.Writers.HashFit3
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrB7
import Proof.Wire_3_5.Primitive.Writers.ThrBud2
import Proof.Wire_3_5.Primitive.Writers.ThrLf2
import Proof.Wire_3_5.Primitive.Writers.ThrSide1
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf3
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf4
import Proof.Wire_3_5.Primitive.SeedFix.C4LeafA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Primitive.SeedFix.TS4L
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashSetH2Base
import Proof.Wire_3_5.Primitive.Writers.KWT2


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 HASH budget and obligations, v3: T-c at `qCost2`

`hash_steps_gen` (M66) against `HashStepsAt3` (the setup's cost `hashC0Q`, the copy `1^{Q'}` at `qCost2 = 14q + 14`):
the only change is the rate-1 extras' constant (`2·pre + cpZ + qCost2 ≤ (730·2^{C_c} + 76)·2^{⌊n/8⌋}`); and `hobl3`,
exactly `c4Leaf_of_obl3`'s `hobl`.
* **`hash_steps_gen2`**, **`hobl3`**.

Paper quantity of the main type: the HASH stage's steps against the seed-fixing budget (P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- **(C), v2 (`QCopy2`): the HASH stage's steps within `c₄·seedClasses E₄`** at every THR call of every call family, at the HASH
leaf's instance, once the THR and HASH free numbers fit the capacity `2^{⌊n/8⌋ + C_c}`. -/
theorem hash_steps_gen2 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
    (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (Cnw Dnw : ℕ)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) (EW E₄ : Envelope) (cW : ℕ)
    (hEc : EW.cpsi ≤ E₄.cpsi) (hEa : EW.Apre ≤ E₄.Apre) (hAt : Dp + 1 ≤ E₄.Atable) (Wk : PrimT.C4KW.KWW) (Cc : ℕ)
    (hfits : ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) → ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
        ThrCap.ThrFitAt H.Fp F.cr F.filterErrDeg (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers translation hs ∧
        ThrCap.HashFitX H.Fp (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) :
    ∃ c₄ : ℕ, ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (S3 : PrimT.C3ReqIface.C3Stage) (fT : ℕ),
      PrimT.C4HL.HashStepsAt3 l F wa K3 D3 Kp Dp H EW cW kclk coef A a0 ha0 (PrimT.C4SymLf.symLay wa S3 (PrimT.C4HL.hDl l Dnw)) (Cnw + 1) (PrimT.C4HL.hCd l F Cnw) Cc (PrimT.TS4.stage4At l F kclk coef A a0 ha0)
        (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg) (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D) Wk fT E₄ c₄ := by
  -- the constants, all before the call
  obtain ⟨cF, hcF⟩ := front_ex (PrimT.C4HL.hDl l Dnw + 16) (Cnw + 1) (PrimT.C4HL.hCd l F Cnw) Cc (ThrSide.stripC l) (ThrSide.stripD l)
  obtain ⟨c3p, hc3p⟩ := ex_poly (((PrimT.C4HL.hDl l Dnw + 16) + 1) * PrimT.TS4.DcG l)
  obtain ⟨c2, hc2⟩ := ex_poly (2 * (Dnw + ThrSide.stripD l))
  obtain ⟨Kc, hKc⟩ := H.cost_le
  obtain ⟨cl, hcl⟩ := ex_s (6 * (ThrSide.eQT l F.filterErrDeg + 1))
  obtain ⟨c1, hc1⟩ := ex_poly 1
  obtain ⟨K0, hK0⟩ := PrimT.C4Cap.mul_sq_le_div16 (2 * F.cr + 2)
  obtain ⟨Kq, hKq⟩ := PrimT.C4Cap.mul_sq_le_div16 (2 * (ThrSide.eQT l F.filterErrDeg + 1))
  obtain ⟨Ks, hKs⟩ := PrimT.C4Cap.mul_sq_le_div16 (8 * (FinalPass.HashFr.cT l * FinalPass.HashFr.cL0 l))
  obtain ⟨K1, hK1⟩ := PrimT.C4Cap.mul_sq_le_div16 Dp
  obtain ⟨cX, hcX⟩ := hX_ex l F Wk (PrimT.C4HL.hDl l Dnw + 16) (PrimT.C4HL.hCd l F Cnw) Cc
  obtain ⟨KF, hKF⟩ : ∃ x, x = 2 ^ cF := ⟨_, rfl⟩
  obtain ⟨KN, hKN⟩ : ∃ x, x = PrimT.TS4.CcG l F.cr * (2 * (Cnw + 1) + (PrimT.C4HL.hCd l F Cnw) + 2) ^ PrimT.TS4.DcG l * 2 ^ c3p :=
    ⟨_, rfl⟩
  obtain ⟨KH, hKH⟩ : ∃ x, x = 460 * ((Cnw + ThrSide.stripC l + 12) * (Cnw + ThrSide.stripC l + 12) * 2 ^ c2) + 40020 :=
    ⟨_, rfl⟩
  obtain ⟨KU, hKU⟩ : ∃ x, x = 19 * 2 ^ Cc := ⟨_, rfl⟩
  obtain ⟨KC, hKC⟩ : ∃ x, x = (3000000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) := ⟨_, rfl⟩
  obtain ⟨KL, hKL⟩ : ∃ x, x = 2 ^ cl := ⟨_, rfl⟩
  obtain ⟨KR, hKR⟩ : ∃ x, x = 2 ^ Cc := ⟨_, rfl⟩
  obtain ⟨KS, hKS⟩ : ∃ x, x = 80 * 2 ^ Cc + 34 := ⟨_, rfl⟩
  obtain ⟨KP, hKP⟩ : ∃ x, x = 730 * 2 ^ Cc + 76 := ⟨_, rfl⟩
  obtain ⟨Kl, hKl⟩ : ∃ x, x = Kq + 1 + (Ks + 1) := ⟨_, rfl⟩
  refine ⟨2 ^ (Nat.clog 2 (KF + (KN + 2 * KH + 22 * 2 ^ Cc + 49) + 34 * KU + 22 * 2 ^ Cc + 2 * KC + 600 * KL +
        40 * 2 ^ c1 + 40 * KR + KS + (2 * KF + KN + KP + 80 * Kl * 2 ^ c1) + 400) + cX + 1 + K0) +
        (32 * (Kl + 1) + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + c1 + 1)) + cW, ?_⟩
  intro kclk coef A a0 ha0 S3 fT
  unfold PrimT.C4HL.HashStepsAt3
  intro n a ha Cs carriers translation hcall hs Bm Sm hcf hBm
  obtain ⟨hfit, hfx⟩ := hfits kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs
  obtain ⟨hk2, hdesc, henv⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn := PrimAsm.CallIndex.n_ge_two l F hs
  have hX1 : 1 ≤ 2 ^ (n / 8) := Nat.one_le_two_pow
  have hM : (2 ^ PrimT.C4Cap.capExp2 Cc n) = 2 ^ Cc * 2 ^ (n / 8) := by unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  have hMc : 1 ≤ 2 ^ Cc := Nat.one_le_two_pow
  -- the front
  have hF : PrimT.C4Cap.frontCost3 (PrimT.C4SymLf.symLay wa S3 (PrimT.C4HL.hDl l Dnw)) (thrReq n a ha Cs carriers translation).word n (Cnw + 1) (PrimT.C4HL.hCd l F Cnw) Cc ≤ KF * 2 ^ (n / 8) := by
    obtain ⟨hwl, -, -, -, -, -⟩ := ThrBud.w_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
    rw [List.length_append] at hwl
    have h := hcF (PrimT.C4SymLf.symLay wa S3 (PrimT.C4HL.hDl l Dnw)) rfl n (thrReq n a ha Cs carriers translation).word (le_trans (by omega) (ThrSide.stripP_le l n))
    have h2 := ex_of h
    rw [one_mul] at h2
    rw [hKF]; exact h2
  -- the data stage
  have hN : (PrimT.TS4.stage4At l F kclk coef A a0 ha0).cost3 a Cs carriers (UnaryCalc.value (PrimT.C4SymLf.symLay wa S3 (PrimT.C4HL.hDl l Dnw)).D (Cnw + 1) n) (UnaryCalc.value (PrimT.C4SymLf.symLay wa S3 (PrimT.C4HL.hDl l Dnw)).D (PrimT.C4HL.hCd l F Cnw) n) ≤
      KN * 2 ^ (n / 8) := by
    rw [hKN]
    exact ThrBud.n3_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs (PrimT.TS4.stage4At l F kclk coef A a0 ha0) (PrimT.TS4.CcG l F.cr)
      (PrimT.TS4.DcG l) le_rfl le_rfl (PrimT.C4HL.hDl l Dnw + 16) (Cnw + 1) (PrimT.C4HL.hCd l F Cnw) (ThrLf.thr_hWL l Cnw Dnw hnw n) c3p (hc3p n)
  -- the hash bits
  have hH : ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n)
      translation.length ([] : List Bool).length (RepairRepresentation.natListWord translation).length ≤ KH * 2 ^ (n / 8) := by
    obtain ⟨hwl, htl, hnl, hbl, hkb, hns⟩ := ThrBud.w_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
    have hcod : (ReqBridge.thrCodes Cs).length = a := List.length_ofFn
    have hcar : (carriers.map Carrier.code).length = carriers.length := List.length_map _
    obtain ⟨Nv, hNv⟩ : ∃ x, x = PrimT.C4GateSym.needW n + ThrSide.stripP l n := ⟨_, rfl⟩
    have h1 := ThrBud.hbXCost_le n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length
      (PrimT.C4GateSym.needW n) translation.length ([] : List Bool).length
      (RepairRepresentation.natListWord translation).length Nv (by rw [hcod]; exact ha) (by rw [hcar]; omega)
      (by omega) (by omega) (by omega) (by simp) (by omega)
    have hQ := ThrBud.nsq_le l Cnw Dnw c2 n (hnw n) (hc2 n)
    rw [← hNv] at hQ
    have h2 : ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n)
        translation.length ([] : List Bool).length (RepairRepresentation.natListWord translation).length ≤
        460 * ((Nv + 12) * (Nv + 12)) + 40020 := by omega
    rw [hKH]
    exact ThrBud.lin_le h2 hQ hX1
  -- the counts
  have hU := ThrBud.u_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs Cc hfit.fhn
  rw [← hKU] at hU
  -- the numbers machine
  have fcP' := hfit.fcP
  rw [pow_succ, pow_succ, pow_succ] at fcP'
  have pw1 : 1 ≤ 2 ^ natBitLength n := Nat.one_le_two_pow
  have pw2 : 1 ≤ 2 ^ natBitLength (ReqBridge.thrCodes Cs).length := Nat.one_le_two_pow
  have pw3 : 1 ≤ 2 ^ natBitLength (List.map Carrier.code carriers).length := Nat.one_le_two_pow
  have hcp : n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2 := by omega
  have hKb : PrimT.C4GateSym.needW n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2 := by omega
  have ht12 : (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD 12 0 ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2 := by
    have := HashFit.getD_le (l := (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) (q := (2 ^ PrimT.C4Cap.capExp2 Cc n))
      (fun v hv => by have := hfit.fhn v (List.mem_append_left _ hv); omega) 12
    omega
  have hc := hc_le l F kclk coef A a0 ha0 ha Cs carriers hs hk2 H.Fp Kc hKc Cc hcp hKb ht12
  rw [← hKC] at hc
  -- the modulus searches, the pad's exponent
  have hl := ThrBud.l_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs cl (hcl n)
  rw [← hKL] at hl
  have hρx := ThrBud.rho_le Cc n _ (hfx.fv 6)
  rw [← hKR] at hρx
  -- the loop's bound and the finisher
  have hcaps := H.caps_ge kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs
  have hf1 := hfx.fv 1
  have hf2 := hfx.fv 2
  have hwd := hfit.fwd
  rw [List.length_append] at hwd
  have hsh : (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n) := by omega
  have hl0 : 1 ≤ (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0 := Nat.one_le_iff_ne_zero.mpr (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0_ne_zero
  have ht2 : 2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t ≤ (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) := Nat.le_mul_of_pos_right _ hl0
  have hs' : PrimT.C4Hk.finCost (thrReq n a ha Cs carriers translation).word (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a0 ha0).starParams n hs) (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation) Cs
      carriers ((callInputs l F kclk coef A a0 ha0).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) ≤ KS * 2 ^ (n / 8) := by
    unfold PrimT.C4Hk.finCost
    rw [List.length_ofFn]
    have hb : 2 * (thrMajorant ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers ((callInputs l F kclk coef A a0 ha0).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)
        (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)).t *
        (thrMajorant ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers ((callInputs l F kclk coef A a0 ha0).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs)
        (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers)).ell0
        ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n) := hsh
    rw [hKS, hM] at *
    have e : (80 * 2 ^ Cc + 34) * 2 ^ (n / 8) = 80 * (2 ^ Cc * 2 ^ (n / 8)) + 34 * 2 ^ (n / 8) := by ring
    omega
  -- the rate-1 extras
  have hP : 2 * PrimT.C4Hk.preCost (thrReq n a ha Cs carriers translation).word (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t) (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) +
      PrimT.C4Set.cpZCost (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ++
        ThrData.thrCounts Cs carriers)) + PrimT.C4KW.qCost2 (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) ≤ KP * 2 ^ (n / 8) := by
    have hu' : (Data.unaryList (ThrData.hashNums ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ++
        ThrData.thrCounts Cs carriers)).length ≤ KU * 2 ^ (n / 8) := hU
    unfold PrimT.C4Hk.preCost PrimT.C4Set.cpZCost CellLoopD.cpCost PrimT.C4KW.qCost2
    rw [hKP, hM] at *
    rw [hKU] at hu'
    have e : (730 * 2 ^ Cc + 76) * 2 ^ (n / 8) = 84 * (2 ^ Cc * 2 ^ (n / 8)) + 646 * (2 ^ Cc * 2 ^ (n / 8)) +
        76 * 2 ^ (n / 8) := by ring
    have e2 : 19 * 2 ^ Cc * 2 ^ (n / 8) = 19 * (2 ^ Cc * 2 ^ (n / 8)) := by ring
    omega
  -- the cell and the writer
  have hX := hcX kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs Bm Sm (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 1) hcf hBm (by omega)
  -- the loop's bound, linear in `n`
  have hlin1 := ThrBud.lin_ell l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs Kq (hKq n)
  have hshl : (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) ≤ (Ks + 1) * (n + 1) := by
    have htt := FinalPass.HashFr.t_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
    have hll := FinalPass.HashFr.ell0_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
    have htt' : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t ≤ FinalPass.HashFr.cT l * (Nat.clog 2 (n + 2) + 1) := htt
    have h1 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0 ≤ (FinalPass.HashFr.cT l * (Nat.clog 2 (n + 2) + 1)) *
        (FinalPass.HashFr.cL0 l * (Nat.clog 2 (n + 2) + 1)) := Nat.mul_le_mul htt' hll
    have h2 := HashFit.clogsq_le n
    have e1 : (FinalPass.HashFr.cT l * (Nat.clog 2 (n + 2) + 1)) * (FinalPass.HashFr.cL0 l * (Nat.clog 2 (n + 2) + 1)) =
        (FinalPass.HashFr.cT l * FinalPass.HashFr.cL0 l) * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)) := by ring
    have h3 : (FinalPass.HashFr.cT l * FinalPass.HashFr.cL0 l) * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)) ≤
        (FinalPass.HashFr.cT l * FinalPass.HashFr.cL0 l) * (4 * PrimT.C4Cap.bsq n) := Nat.mul_le_mul_left _ h2
    have h4 := hKs n
    have e2 : 8 * (FinalPass.HashFr.cT l * FinalPass.HashFr.cL0 l) * (natBitLength n + 1) ^ 2 =
        2 * ((FinalPass.HashFr.cT l * FinalPass.HashFr.cL0 l) * (4 * PrimT.C4Cap.bsq n)) := by
      unfold PrimT.C4Cap.bsq; ring
    have e3 : (Ks + 1) * (n + 1) = Ks * n + Ks + n + 1 := by ring
    have e4 : (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) = 2 * ((PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) := by ring
    omega
  have hlin : (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) + (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0) ≤ Kl * (n + 1) := by
    rw [hKl]
    have e : (Kq + 1 + (Ks + 1)) * (n + 1) = (Kq + 1) * (n + 1) + (Ks + 1) * (n + 1) := by ring
    omega
  have hb : (PrimT.C4Hf.hashFamCall (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation UnionMachine.TailAsm.asmStage wa
      (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4)
        (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 rfl rfl rfl
      (FinalPass.HashFr.capsOf (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 1)) E₄ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) (H.Kc n) (H.Kch n)
      (H.caps_ge kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs)
      (H.side kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs)).F.bound ≤ 8 * ((max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) + (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0)) := by
    rw [(PrimT.C4Hf.hashFamCall (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation UnionMachine.TailAsm.asmStage wa
      (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4)
        (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0 rfl rfl rfl
      (FinalPass.HashFr.capsOf (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 1)) E₄ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) (H.Kc n) (H.Kch n)
      (H.caps_ge kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs)
      (H.side kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs)).bound]
    omega
  have hk : ((gate0 l F).budget kclk coef A a0 ha0).kOf n ≤ n / 16 + K0 :=
    le_trans (PrimT.C4SymN.kOf_le_bsq l F kclk coef A a0 ha0 n) (hK0 n)
  have hkn : ((gate0 l F).budget kclk coef A a0 ha0).kOf n ≤ n := ((callInputs l F kclk coef A a0 ha0).starParams n hs).k_le_n
  have hK2 : n + 1 ≤ 2 ^ (n / 8 + c1) := by
    have q := hc1 n
    unfold Ex at q
    rw [pow_one, one_mul] at q
    exact q
  exact hash_steps_core E₄ EW (PrimT.C4SymLf.symLay wa S3 (PrimT.C4HL.hDl l Dnw)) (thrReq n a ha Cs carriers translation).word n (Cnw + 1) (PrimT.C4HL.hCd l F Cnw) Cc _ _ _ _ (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) _ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) _ _
    (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n) ((max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) + (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0)) _
    (PrimT.C4Hk.preCost (thrReq n a ha Cs carriers translation).word (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t) (2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0)) _ _ _ _ cW Kp Dp K0 K1 c1 Kl KF KN KH KU KC KL KR KS KP cX
    (H.side kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs).2.2.2.2.2.1 hb hF hN hH hU hc hl hρx hs' hP hX
    (by omega) hk hkn hlin (d2_le _) (H.pad_le kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs) (hK1 n) hK2
    le_rfl hEc hEa hAt

/-- **The HASH obligations at every admissible `F`, v3** (`c4Leaf_of_obl3`'s `hobl`), for any kept words writer. -/
noncomputable def hobl3 (Wk : PrimT.C4KW.KWW) : ∀ (l : Literals) (fe CDs K3 D3 Kp Dp : ℕ) (F : GateFree l)
    (H : FinalPass.HashFr.HashFreeOk2 l F (PrimT.C4LeafA.waOf l) K3 D3 Kp Dp) (EW : Envelope) (cW : ℕ)
    (W : ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1), C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0),
    F.filterErrDeg = fe → ClassLE (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) F.E →
    PrimT.C4HL.HashObl3 l F (PrimT.C4LeafA.waOf l) K3 D3 Kp Dp H EW cW W PrimT.C4HL.cnw PrimT.C4HL.dnw Wk
      (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) :=
  fun l fe CDs K3 D3 Kp Dp F H EW cW W hfe hE =>
    have hwb := (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2
    have hnw := (Classical.choose_spec (Classical.choose_spec PrimT.C4GateSym.needW_pb)).2
    have hfits := HashFit.hash_fits l F H.Fp H.ok_le H.val_le H.rho_le (Classical.choose CallSize.wordBound_poly)
      (Classical.choose (Classical.choose_spec CallSize.wordBound_poly)) PrimT.C4HL.cnw PrimT.C4HL.dnw hwb hnw
    have hEc : EW.cpsi ≤ (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)).cpsi :=
      (PrimT.C4K.le_emax_left EW (PrimT.C4SymLf.symFloor Dp)).cpsi
    have hEa : EW.Apre ≤ (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)).Apre :=
      (PrimT.C4K.le_emax_left EW (PrimT.C4SymLf.symFloor Dp)).Apre
    have hAt : Dp + 1 ≤ (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)).Atable :=
      (PrimT.C4K.le_emax_right EW (PrimT.C4SymLf.symFloor Dp)).Atable
    have hst := hash_steps_gen2 l F (PrimT.C4LeafA.waOf l) K3 D3 Kp Dp H PrimT.C4HL.cnw PrimT.C4HL.dnw hnw EW
      (PrimT.C4K.emax EW (PrimT.C4SymLf.symFloor Dp)) cW hEc hEa hAt Wk (Classical.choose hfits)
      (fun kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs =>
        ⟨(Classical.choose_spec hfits (Classical.choose hfits) le_rfl kclk coef A a0 ha0 n a ha Cs carriers translation
          hcall hs).1,
         (Classical.choose_spec hfits (Classical.choose hfits) le_rfl kclk coef A a0 ha0 n a ha Cs carriers translation
          hcall hs).2.1⟩)
    ⟨Classical.choose hfits, Classical.choose hst,
      fun kclk coef A a0 ha0 => by
        unfold PrimT.C4HL.HashSideAt2
        intro n a ha Cs carriers translation hcall hs
        obtain ⟨hfit, hfx, Bm, Sm, hcf, hBm⟩ := Classical.choose_spec hfits (Classical.choose hfits) le_rfl kclk coef A
          a0 ha0 n a ha Cs carriers translation hcall hs
        obtain ⟨hrP, hn1, hcapT, hok, hnd⟩ := HashFit.side_ok l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
          PrimT.C4HL.cnw PrimT.C4HL.dnw (hnw n) (PrimT.C4LeafA.waOf l) (W kclk coef A a0 ha0).thr
        exact ⟨hfit, hfx,
          PrimT.C4HL.hash_h1 l F (PrimT.C4LeafA.waOf l) K3 D3 Kp Dp H kclk coef A a0 ha0 ha Cs carriers translation hcall hs,
          PrimT.C4HL.hash_hcf l F (PrimT.C4LeafA.waOf l) K3 D3 Kp Dp H kclk coef A a0 ha0 ha Cs carriers translation hcall
            hs, hrP, hn1, hcapT, hok, hnd, Bm, Sm, hcf, hBm⟩,
      fun kclk coef A a0 ha0 => Classical.choose_spec hst kclk coef A a0 ha0 (W kclk coef A a0 ha0).thr
        (PrimT.C4Hk.famUH UnionMachine.TailAsm.asmStage (PrimT.C4LeafA.waOf l)).T⟩

end NearCubicWires.WireExponent3_5.PrimAsm.HashBud

end
