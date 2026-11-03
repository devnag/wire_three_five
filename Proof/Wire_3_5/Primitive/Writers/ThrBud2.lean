import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrBud1
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrB7
import Proof.Wire_3_5.Primitive.Writers.ThrSide1
import Proof.Wire_3_5.Primitive.Writers.ThrSide2
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 8 part 2: `thr_steps_gen` (the THR stage's `hBd`)

The THR twin of the `sym_steps_gen` (C4BudF): at every THR call where the numbers fit the capacity v2 (`ThrFitAt` at
`M = 2^{capExp2 C_c n}`, `thr_fits2`), the THR stage's steps (`thr_stage_of_big`'s `hBd`: the setup at the THR
input `req.word ++ hbF`, the data stage `S.cost3`, the hash bits, the numbers machine `thrBigCost`, the strip's C3
budget `thrB`, the loop over any child family whose cells fit the pad, the finisher) are within `c₄·seedClasses E₄`,
`c₄` after `F` (P3:3098-3100, 3105-3115).
* **`thr_ell_le`** (`ℓ ≤ 2(e_Q+1)·bsq n`, `Q ≤ 2^{2e_Q·bsq n}`, `k_h ≤ bsq n`), `w_le` (`|req.word ++ hbF|`, the translation's
  words and `kbT n` within the strip polynomial), **`thr_steps_gen`**.

Paper quantity of the main type: the THR stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (k_le_L2 kh_two)

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The THR modulus length, count and half-width** within `bsq n`. -/
theorem thr_ell_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (max (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ 2 * (ThrSide.eQT l F.filterErrDeg + 1) * PrimT.C4Cap.bsq n ∧
      (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell ≤ 2 * (ThrSide.eQT l F.filterErrDeg + 1) * PrimT.C4Cap.bsq n ∧
      SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤ 2 ^ (2 * ThrSide.eQT l F.filterErrDeg * PrimT.C4Cap.bsq n) ∧
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤ PrimT.C4Cap.bsq n := by
  have hq := ThrSide.thrCount_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hk := k_le_L2 l F kclk coef A a ha hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hL : Nat.clog 2 (n + 2) ≤ natBitLength n + 1 := PrimT.C4Cap.lq_le n
  have hb1 := PrimT.C4Cap.b1_le_bsq n
  have hL2 : Nat.clog 2 (n + 2) ^ 2 ≤ PrimT.C4Cap.bsq n := Nat.pow_le_pow_left hL 2
  obtain ⟨e, he⟩ : ∃ e, e = ThrSide.eQT l F.filterErrDeg := ⟨_, rfl⟩
  rw [← he] at hq ⊢
  have hKL : ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) ≤ 2 * PrimT.C4Cap.bsq n := by omega
  have hq2 : SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs ≤ 2 ^ (2 * e * PrimT.C4Cap.bsq n) := by
    refine hq.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have := Nat.mul_le_mul_left e hKL
    have e2 : e * (2 * PrimT.C4Cap.bsq n) = 2 * e * PrimT.C4Cap.bsq n := by ring
    omega
  have hcl : Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) ≤ 2 * e * PrimT.C4Cap.bsq n :=
    Nat.clog_le_of_le_pow hq2
  have hbp := PrimT.C4Cap.bsq_pos n
  have e3 : 2 * (e + 1) * PrimT.C4Cap.bsq n = 2 * e * PrimT.C4Cap.bsq n + 2 * PrimT.C4Cap.bsq n := by ring
  have hkb : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤ PrimT.C4Cap.bsq n := by omega
  refine ⟨by omega, ?_, hq2, hkb⟩
  show max 1 (max (2 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ _
  omega

/-- **The THR input word, the translation's words and `kbT`** within the strip polynomial. -/
theorem w_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length ≤ ThrSide.stripP l n ∧ translation.length ≤ ThrSide.stripP l n ∧
      (RepairRepresentation.natListWord translation).length ≤ ThrSide.stripP l n ∧
      (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length ≤ ThrSide.stripP l n ∧ ThrFam.kbT n ≤ ThrSide.stripP l n ∧ n ≤ ThrSide.stripP l n := by
  have hw : (thrReq n a' ha' Cs carriers translation).word.length ≤ CallSize.wordBound 26 26 2 n :=
    CallSize.gate_word_length_le l F kclk coef A a ha _ hcall
  have hb := ThrSide.hbC_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have htr : 8 * translation.length + 2 * (RepairRepresentation.natListWord translation).length + 16 ≤
      8 * n + 2 * ((2 * n + 3) * (n + 1)) + 16 := ThrSide.strip_req _ _ hcall
  have hL : Nat.clog 2 (n + 2) ≤ n + 1 := Nat.clog_le_of_le_pow (by
    have := Nat.lt_two_pow_self (n := n + 1)
    rw [pow_succ] at this ⊢; omega)
  have hLL : Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hL hL
  have hcL : ThrSide.cH l * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) ≤ ThrSide.cH l * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left _ hLL
  have hwb : 8 * n + 2 * ((2 * n + 3) * (n + 1)) ≤ 10 * ((2 * n + 3) * (n + 1)) := by nlinarith
  unfold ThrSide.stripP
  rw [List.length_append]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The front at rate `1`** (the `front_ex` at the strip polynomial's bound). -/
theorem front_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (D CL Cd Cc cF : ℕ)
    (hcF : ∀ (L : Lay), L.D = D → ∀ (n : ℕ) (w : List Bool), w.length ≤ ThrSide.stripC l * (n + 1) ^ ThrSide.stripD l →
      Ex n 1 cF (PrimT.C4Cap.frontCost3 L w n CL Cd Cc)) (L : Lay) (hLD : L.D = D) :
    PrimT.C4Cap.frontCost3 L ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)) n CL Cd Cc ≤ 2 ^ cF * 2 ^ (n / 8) := by
  have h := hcF L hLD n _ ((w_le l F kclk coef A a ha ha' Cs carriers translation hcall hs).1.trans
    (ThrSide.stripP_le l n))
  have h2 := ex_of h
  rwa [one_mul] at h2

/-- **The THR data stage at rate `1`** (the stage's polynomial bound at the unary numbers `C(n+1)^D`). -/
theorem n3_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (_hs : (callInputs l F kclk coef A a ha).StarAt n) (S0 : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap)) (C3 D3 : ℕ) (hC3 : S0.Cc3 ≤ C3) (hD3 : S0.Dc3 ≤ D3) (D CL Cd : ℕ)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value D CL n) (c3p : ℕ) (hc3p : Ex n 1 c3p ((n + 1) ^ ((D + 1) * D3))) :
    (S0.cost3 a' Cs carriers (UnaryCalc.value D CL n) (UnaryCalc.value D Cd n)) ≤ (C3 * (2 * CL + Cd + 2) ^ D3 * 2 ^ c3p) * 2 ^ (n / 8) := by
  obtain ⟨hk2, hdesc, he⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  obtain ⟨hL, hLX, h2, -, -, -, -, -, -, hK, hKX⟩ := PrimT.C4GateSym.thr_data_hyps Cs carriers ha' hk2 hdesc he
    (UnaryCalc.value D CL n) hWL
  have hpoly := S0.cost3_le Cs carriers (UnaryCalc.value D CL n) (UnaryCalc.value D Cd n) (UnaryCalc.value D CL n) ha' hk2
    hL hLX hK hKX h2
  unfold ValidatorPolynomialDomination.PolyBounded at hpoly
  have p1 : (n + 1) ^ D ≤ (n + 1) ^ (D + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : n + 1 ≤ (n + 1) ^ (D + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : UnaryCalc.value D CL n + n + UnaryCalc.value D CL n + UnaryCalc.value D Cd n + 1 ≤
      (2 * CL + Cd + 2) * (n + 1) ^ (D + 1) := by
    unfold UnaryCalc.value
    have a1 : CL * (n + 1) ^ D ≤ CL * (n + 1) ^ (D + 1) := Nat.mul_le_mul_left _ p1
    have a2 : Cd * (n + 1) ^ D ≤ Cd * (n + 1) ^ (D + 1) := Nat.mul_le_mul_left _ p1
    have e : (2 * CL + Cd + 2) * (n + 1) ^ (D + 1) = 2 * (CL * (n + 1) ^ (D + 1)) + Cd * (n + 1) ^ (D + 1) +
        2 * (n + 1) ^ (D + 1) := by ring
    omega
  have hb1 : 1 ≤ UnaryCalc.value D CL n + n + UnaryCalc.value D CL n + UnaryCalc.value D Cd n + 1 := by omega
  have q1 := ex_of hc3p
  rw [one_mul] at q1
  calc (S0.cost3 a' Cs carriers (UnaryCalc.value D CL n) (UnaryCalc.value D Cd n))
      ≤ S0.Cc3 * (UnaryCalc.value D CL n + n + UnaryCalc.value D CL n + UnaryCalc.value D Cd n + 1) ^ S0.Dc3 := hpoly
    _ ≤ C3 * (UnaryCalc.value D CL n + n + UnaryCalc.value D CL n + UnaryCalc.value D Cd n + 1) ^ D3 :=
        Nat.mul_le_mul hC3 (Nat.pow_le_pow_right hb1 hD3)
    _ ≤ C3 * ((2 * CL + Cd + 2) * (n + 1) ^ (D + 1)) ^ D3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = C3 * (2 * CL + Cd + 2) ^ D3 * (n + 1) ^ ((D + 1) * D3) := by rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ C3 * (2 * CL + Cd + 2) ^ D3 * (2 ^ c3p * 2 ^ (n / 8)) := Nat.mul_le_mul_left _ q1
    _ = _ := by ring

/-- **The polynomial `N = needW + stripP`, squared, at rate `1`.** -/
theorem nsq_le (l : Literals) (Cnw Dnw c2 n : ℕ) (hnw : PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw)
    (hc2 : Ex n 1 c2 ((n + 1) ^ (2 * (Dnw + ThrSide.stripD l)))) :
    (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12) * (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12) ≤
      ((Cnw + ThrSide.stripC l + 12) * (Cnw + ThrSide.stripC l + 12) * 2 ^ c2) * 2 ^ (n / 8) := by
  have hsP := ThrSide.stripP_le l n
  have a1 : Cnw * (n + 1) ^ Dnw ≤ Cnw * (n + 1) ^ (Dnw + ThrSide.stripD l) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have a2 : ThrSide.stripC l * (n + 1) ^ ThrSide.stripD l ≤ ThrSide.stripC l * (n + 1) ^ (Dnw + ThrSide.stripD l) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have a3 : 1 ≤ (n + 1) ^ (Dnw + ThrSide.stripD l) := Nat.one_le_pow _ _ (by omega)
  have hNn : (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12) ≤ (Cnw + ThrSide.stripC l + 12) * (n + 1) ^ (Dnw + ThrSide.stripD l) := by
    have e : (Cnw + ThrSide.stripC l + 12) * (n + 1) ^ (Dnw + ThrSide.stripD l) = Cnw * (n + 1) ^ (Dnw + ThrSide.stripD l) +
        ThrSide.stripC l * (n + 1) ^ (Dnw + ThrSide.stripD l) + 12 * (n + 1) ^ (Dnw + ThrSide.stripD l) := by ring
    omega
  have q := ex_of hc2
  rw [one_mul] at q
  calc (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12) * (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12)
      ≤ ((Cnw + ThrSide.stripC l + 12) * (n + 1) ^ (Dnw + ThrSide.stripD l)) *
        ((Cnw + ThrSide.stripC l + 12) * (n + 1) ^ (Dnw + ThrSide.stripD l)) := Nat.mul_le_mul hNn hNn
    _ = (Cnw + ThrSide.stripC l + 12) * (Cnw + ThrSide.stripC l + 12) * (n + 1) ^ (2 * (Dnw + ThrSide.stripD l)) := by
        rw [two_mul, pow_add]; ring
    _ ≤ (Cnw + ThrSide.stripC l + 12) * (Cnw + ThrSide.stripC l + 12) * (2 ^ c2 * 2 ^ (n / 8)) :=
        Nat.mul_le_mul_left _ q
    _ = _ := by ring

/-- **The hash bits' steps and the strip's own inputs** below `460·N² + 40020`. -/
theorem hbx_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Q : ℕ) (hQ : (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12) * (PrimT.C4GateSym.needW n + ThrSide.stripP l n + 12) ≤ Q) :
    (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length) ≤ 460 * Q + 40020 ∧ (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (ThrFam.kbT n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length + 60 * ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length + 20) ≤ 460 * Q + 40020 := by
  obtain ⟨hwl, htl, hnl, hbl, hkb, hns⟩ := w_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hcod : (ReqBridge.thrCodes Cs).length = a' := List.length_ofFn
  have hcar : (carriers.map Carrier.code).length = carriers.length := List.length_map _
  obtain ⟨Nv, hNv⟩ : ∃ x, x = PrimT.C4GateSym.needW n + ThrSide.stripP l n := ⟨_, rfl⟩
  have h3 : Nv ≤ (Nv + 12) * (Nv + 12) := by nlinarith
  have hQ' : (Nv + 12) * (Nv + 12) ≤ Q := by rw [hNv]; exact hQ
  have hH0 : ∀ Kb, Kb ≤ Nv →
      ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length Kb translation.length
        (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length ≤ 400 * ((Nv + 12) * (Nv + 12)) + 40000 :=
    fun Kb hKb => hbXCost_le _ _ _ _ _ _ _ _ (by rw [hcod]; exact ha') (by rw [hcar]; omega) (by omega) hKb (by omega)
      (by omega) (by omega)
  have g1 := hH0 (PrimT.C4GateSym.needW n) (by omega)
  have g2 := hH0 (ThrFam.kbT n) (by omega)
  refine ⟨by omega, by omega⟩

/-- **The counts' unary word** at rate `1`. -/
theorem u_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Cc : ℕ) (fhn : ∀ v ∈ (ThrCap.hnC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs ++ ThrData.thrCounts Cs carriers), v + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n)) :
    (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs ++ ThrData.thrCounts Cs carriers)).length ≤ (19 * 2 ^ Cc) * 2 ^ (n / 8) := by
  have h1 := unary_le _ _ fhn
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hl : (ThrCap.hnC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs ++ ThrData.thrCounts Cs carriers).length ≤ 19 := by
    rw [List.length_append, ThrData.hashNums_length]
    unfold ThrData.thrCounts
    rw [List.length_append, List.length_map, List.length_singleton]
    omega
  have hM : (2 ^ PrimT.C4Cap.capExp2 Cc n) = 2 ^ Cc * 2 ^ (n / 8) := by unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  rw [hM] at h1
  calc _ ≤ _ := h1
    _ ≤ 19 * (2 ^ Cc * 2 ^ (n / 8)) := Nat.mul_le_mul_right _ hl
    _ = _ := by ring

/-- **The THR numbers machine at rate `3`** (quadratic in the capacity, a free program quadratic too). -/
theorem c_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Fp : FreeProg) (Kc : ℕ) (hKc : ∀ (cap : ℕ) (x : FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2)
    (Cc : ℕ) (hn : n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (hKb : PrimT.C4GateSym.needW n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) :
    (ThrCap.thrBigCost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))) ≤ ((300000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc)) * 2 ^ (3 * (n / 8)) := by
  have hk2 : carriers.length ≤ 2 := hcall.2.2.2.1
  have hcod : (ReqBridge.thrCodes Cs).length = a' := List.length_ofFn
  have hcar : (carriers.map Carrier.code).length = carriers.length := List.length_map _
  have h1 := thrBig_le (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length
    (PrimT.C4GateSym.needW n) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) hn (by rw [hcod]; exact ha')
    (by rw [hcar]; omega) hKb
  have h2 := hKc (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)
  have hB := capB_le Cc n
  obtain ⟨Z, hZ⟩ : ∃ z, z = (2 ^ PrimT.C4Cap.capExp2 Cc n) := ⟨_, rfl⟩
  obtain ⟨Xv, hXv⟩ : ∃ z, z = 2 ^ (n / 8) := ⟨_, rfl⟩
  have hX3 : 2 ^ (3 * (n / 8)) = Xv * Xv * Xv := by rw [hXv]; ring
  rw [← hZ] at h1 h2 hB ⊢
  rw [← hXv] at hB
  rw [hX3]
  have hX1 : 1 ≤ Xv := hXv ▸ Nat.one_le_two_pow
  obtain ⟨G, hG⟩ : ∃ g, g = 6 * 2 ^ Cc * Xv := ⟨_, rfl⟩
  have hZ6 : Z + Z + 2 + 2 ≤ G := by rw [hG]; omega
  have g1 : (2 * Z + 2 + 2) * (2 * Z + 2 + 2) ≤ G * G := Nat.mul_le_mul (by omega) (by omega)
  have g2 : (2 * Z + 2 + 1) ^ 2 ≤ (2 * Z + 2 + 2) * (2 * Z + 2 + 2) := by nlinarith
  have g3 : Xv * Xv ≤ Xv * Xv * Xv := Nat.le_mul_of_pos_right _ (by omega)
  have g4 : Kc * (2 * Z + 2 + 1) ^ 2 ≤ Kc * (G * G) := Nat.mul_le_mul_left _ (g2.trans g1)
  have g5 : 300000 * ((2 * Z + 2 + 2) * (2 * Z + 2 + 2)) ≤ 300000 * (G * G) := Nat.mul_le_mul_left _ g1
  have e1 : (300000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) * (Xv * Xv * Xv) =
      (300000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) * (Xv * Xv * Xv) := rfl
  have g6 : (300000 + Kc) * (G * G) ≤ (300000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) * (Xv * Xv * Xv) := by
    have e : (300000 + Kc) * (G * G) = (300000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) * (Xv * Xv) := by rw [hG]; ring
    rw [e]
    exact Nat.mul_le_mul_left _ g3
  have e2 : (300000 + Kc) * (G * G) = 300000 * (G * G) + Kc * (G * G) := by ring
  omega

/-- **The modulus searches at rate `1`.** -/
theorem l_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (cl : ℕ) (hcl : Ex n 1 cl (2 ^ (6 * (ThrSide.eQT l F.filterErrDeg + 1) * (natBitLength n + 1) ^ 2))) :
    2 ^ (3 * (max (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)))) ≤ 2 ^ cl * 2 ^ (n / 8) := by
  obtain ⟨hl1, -, -, -⟩ := thr_ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have q := ex_of hcl
  rw [one_mul] at q
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) q
  have e : 6 * (ThrSide.eQT l F.filterErrDeg + 1) * (natBitLength n + 1) ^ 2 =
      3 * (2 * (ThrSide.eQT l F.filterErrDeg + 1) * PrimT.C4Cap.bsq n) := by unfold PrimT.C4Cap.bsq; ring
  rw [e]
  omega

/-- **The finisher at rate `1`.** -/
theorem nf_le (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (ce : ℕ) (hce : Ex n 1 ce (2 ^ ((10 * ThrSide.eQT l F.filterErrDeg + 10) * (natBitLength n + 1) ^ 2)))
    (Cc : ℕ) (hbl : (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n)) (s : Fin (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) → Bool) :
    (ThrFin.finCost (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) s (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)) ≤ ((2 ^ 21 + 32) * 2 ^ ce + 16 * 2 ^ Cc) * 2 ^ (n / 8) := by
  have h1 := fin_le (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) s (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)
  have eQd : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).Q = SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs := rfl
  have ekh : (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).kh = SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) := rfl
  rw [eQd, ekh] at h1
  obtain ⟨-, hl2, hq, hkb2⟩ := thr_ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have q := ex_of hce
  rw [one_mul] at q
  have hM : (2 ^ PrimT.C4Cap.capExp2 Cc n) = 2 ^ Cc * 2 ^ (n / 8) := by unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  rw [hM] at hbl
  obtain ⟨B, hBd⟩ : ∃ x, x = PrimT.C4Cap.bsq n := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ x, x = ThrSide.eQT l F.filterErrDeg := ⟨_, rfl⟩
  rw [← hBd] at hl2 hq hkb2
  rw [← he] at hl2 hq
  have eq1 : (10 * ThrSide.eQT l F.filterErrDeg + 10) * (natBitLength n + 1) ^ 2 = (10 * e + 10) * B := by
    rw [he, hBd]; unfold PrimT.C4Cap.bsq; ring
  rw [eq1] at q
  obtain ⟨Q, hQd⟩ : ∃ x, x = SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs := ⟨_, rfl⟩
  obtain ⟨kh, hkhd⟩ : ∃ x, x = SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  obtain ⟨el, held⟩ : ∃ x, x = (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell := ⟨_, rfl⟩
  obtain ⟨Xv, hXv⟩ : ∃ x, x = 2 ^ (n / 8) := ⟨_, rfl⟩
  obtain ⟨hl, hhl⟩ : ∃ x, x = (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length := ⟨_, rfl⟩
  rw [← hQd, ← hkhd, ← held, ← hhl] at h1
  rw [← hQd] at hq
  rw [← hkhd] at hkb2
  rw [← held] at hl2
  rw [← hXv] at q hbl ⊢
  rw [← hhl] at hbl
  have hB1 : B + 1 ≤ 2 ^ B := Nat.lt_two_pow_self
  have b1 : 2 ^ (4 * el) ≤ 2 ^ (8 * (e + 1) * B) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have b2 : Q + 1 ≤ 2 * 2 ^ (2 * e * B) := by have := Nat.one_le_two_pow (n := 2 * e * B); omega
  have b3 : 1048576 * (Q + 1) * 2 ^ (4 * el) ≤ 2 ^ 21 * 2 ^ ((10 * e + 10) * B) := by
    calc 1048576 * (Q + 1) * 2 ^ (4 * el) ≤ 1048576 * (2 * 2 ^ (2 * e * B)) * 2 ^ (8 * (e + 1) * B) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ b2) b1
      _ = 2 ^ 21 * 2 ^ (2 * e * B + 8 * (e + 1) * B) := by rw [pow_add]; ring
      _ ≤ 2 ^ 21 * 2 ^ ((10 * e + 10) * B) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have b4 : 4 * (Q * (5 * kh + 5)) ≤ 20 * 2 ^ ((10 * e + 10) * B) := by
    have c1' : 5 * kh + 5 ≤ 5 * 2 ^ B := by omega
    have c2' : Q * (5 * kh + 5) ≤ 2 ^ (2 * e * B) * (5 * 2 ^ B) := Nat.mul_le_mul hq c1'
    have c3' : 2 ^ (2 * e * B) * 2 ^ B ≤ 2 ^ ((10 * e + 10) * B) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have e2 : 2 ^ (2 * e * B) * (5 * 2 ^ B) = 5 * (2 ^ (2 * e * B) * 2 ^ B) := by ring
    omega
  have q2 : 2 ^ 21 * 2 ^ ((10 * e + 10) * B) ≤ 2 ^ 21 * (2 ^ ce * Xv) := Nat.mul_le_mul_left _ q
  have hce1 : 1 ≤ 2 ^ ce * Xv := Nat.one_le_iff_ne_zero.mpr (by rw [hXv]; positivity)
  have e3 : ((2 ^ 21 + 32) * 2 ^ ce + 16 * 2 ^ Cc) * Xv = 2 ^ 21 * (2 ^ ce * Xv) + 32 * (2 ^ ce * Xv) +
      16 * (2 ^ Cc * Xv) := by ring
  omega

/-- **The modulus length is linear in `n`.** -/
theorem lin_ell (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Kq : ℕ) (hKq : 2 * (ThrSide.eQT l F.filterErrDeg + 1) * (natBitLength n + 1) ^ 2 ≤ n / 16 + Kq) :
    (max (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ (Kq + 1) * (n + 1) := by
  obtain ⟨hl1, -, -, -⟩ := thr_ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have e : 2 * (ThrSide.eQT l F.filterErrDeg + 1) * PrimT.C4Cap.bsq n =
      2 * (ThrSide.eQT l F.filterErrDeg + 1) * (natBitLength n + 1) ^ 2 := rfl
  have e2 : (Kq + 1) * (n + 1) = Kq * n + Kq + n + 1 := by ring
  omega

end Gate

/-- **The THR stage's steps within the seed-fixing budget** at every THR call whose numbers fit the capacity v2,
generic in the free program (its steps quadratic in the capacity, its pad within the classes at `Kp`, `Dp`) and the
data stage family `S` (uniform constants `C3`, `D3`); `c₄` after `F`. -/
theorem thr_steps_gen (l : Literals) (F : GateFree l) (Kp Dp : ℕ) (Fp : FreeProg) (Kc : ℕ)
    (hKc : ∀ (cap : ℕ) (x : FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2)
    (hpad : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
      (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
        2 ^ (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) ≤ Kp * (2 ^ (n - (((gate0 l F).budget kclk coef A a ha).kOf n)) * (n + 1) ^ Dp +
          2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2)))
    (S : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
    (C3 D3 : ℕ) (hS : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), (S kclk coef A a ha).Cc3 ≤ C3 ∧ (S kclk coef A a ha).Dc3 ≤ D3)
    (D CL Cd Cc : ℕ) (hWL : ∀ n, PrimT.C4GateSym.needW n ≤ UnaryCalc.value D CL n)
    (EW E₄ : Envelope) (cW : ℕ) (hEc : EW.cpsi ≤ E₄.cpsi) (hEa : EW.Apre ≤ E₄.Apre) (hAt : Dp + 1 ≤ E₄.Atable) :
    ∃ c₄ : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
      (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ThrCap.ThrFitAt Fp F.cr F.filterErrDeg (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a ha) (gate0 l F).alg ha' Cs carriers translation hs →
      ∀ (L : Lay), L.D = D → ∀ (Fm : PrimT.C4Loop.ChildFam), Fm.cellCost + 1 ≤ 2 ^ (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6) →
      Fm.bound ≤ 8 * (max (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) → ∀ s : Fin (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs).ell) → Bool,
      wrapCost (ThrSet.setupT3Cost L ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)) n CL Cd Cc ((S kclk coef A a ha).cost3 a' Cs carriers (UnaryCalc.value D CL n) (UnaryCalc.value D Cd n)) (2 ^ PrimT.C4Cap.capExp2 Cc n)
          (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length)
          (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs ++ ThrData.thrCounts Cs carriers))
          (ThrCap.thrBigCost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)))
          (max (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs)) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6)
          (ThrStrip.thrB (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n) (((gate0 l F).budget kclk coef A a ha).psiOf n)) (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (ThrFam.kbT n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length + 60 * ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length + 20) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4)))
        Fm (2 ^ (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6)) (ThrFin.finCost (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) s (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)) + 1 ≤
      c₄ * seedClasses E₄ n (((gate0 l F).budget kclk coef A a ha).kOf n) (((gate0 l F).budget kclk coef A a ha).psiOf n) := by
  -- the constants, all before the call
  obtain ⟨Cnw, Dnw, -, hnw⟩ := PrimT.C4GateSym.needW_pb
  obtain ⟨cF, hcF⟩ := front_ex D CL Cd Cc (ThrSide.stripC l) (ThrSide.stripD l)
  obtain ⟨c3p, hc3p⟩ := ex_poly ((D + 1) * D3)
  obtain ⟨c2, hc2⟩ := ex_poly (2 * (Dnw + ThrSide.stripD l))
  obtain ⟨ce, hce⟩ := ex_s (10 * ThrSide.eQT l F.filterErrDeg + 10)
  obtain ⟨cl, hcl⟩ := ex_s (6 * (ThrSide.eQT l F.filterErrDeg + 1))
  obtain ⟨c1, hc1⟩ := ex_poly 1
  obtain ⟨K0, hK0⟩ := PrimT.C4Cap.mul_sq_le_div16 (2 * F.cr + 2)
  obtain ⟨Kq, hKq⟩ := PrimT.C4Cap.mul_sq_le_div16 (2 * (ThrSide.eQT l F.filterErrDeg + 1))
  obtain ⟨K1, hK1⟩ := PrimT.C4Cap.mul_sq_le_div16 Dp
  obtain ⟨KH, hKH⟩ : ∃ x, x = 460 * ((Cnw + ThrSide.stripC l + 12) * (Cnw + ThrSide.stripC l + 12) * 2 ^ c2) + 40020 :=
    ⟨_, rfl⟩
  refine ⟨2 ^ (Nat.clog 2 (2 ^ cF + (C3 * (2 * CL + Cd + 2) ^ D3 * 2 ^ c3p + 2 * KH + 22 * 2 ^ Cc + 49) +
      34 * (19 * 2 ^ Cc) + 22 * 2 ^ Cc + 2 * ((300000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc)) + 600 * 2 ^ cl +
      40 * 2 ^ c1 + 40 * 2 ^ Cc + ((2 ^ 21 + 32) * 2 ^ ce + 16 * 2 ^ Cc) + (28 * 2 ^ Cc + 2 * KH + 51) + 400) + K0) +
    (32 * (Kq + 1) + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + c1 + 1)) + cW, ?_⟩
  intro kclk coef A a ha n a' ha' Cs carriers translation hcall hs hfit L hLD Fm hcell hb s
  obtain ⟨-, fv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fwd, -, fcP, fhn, -, -, -, -, -, -, -, -⟩ := hfit
  have hn := PrimAsm.CallIndex.n_ge_two l F hs
  have hF := front_le l F kclk coef A a ha ha' Cs carriers translation hcall hs D CL Cd Cc cF hcF L hLD
  have hN := n3_le l F kclk coef A a ha ha' Cs carriers translation hcall hs (S kclk coef A a ha) C3 D3
    (hS kclk coef A a ha).1 (hS kclk coef A a ha).2 D CL Cd (hWL n) c3p (hc3p n)
  have hQ := nsq_le l Cnw Dnw c2 n (hnw n) (hc2 n)
  obtain ⟨hH1, hH2⟩ := hbx_le l F kclk coef A a ha ha' Cs carriers translation hcall hs _ hQ
  have hX1 : 1 ≤ 2 ^ (n / 8) := Nat.one_le_two_pow
  have hH : (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length) ≤ KH * 2 ^ (n / 8) := hKH ▸ lin_le hH1 le_rfl hX1
  have hcs : (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (ThrFam.kbT n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length + 60 * ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length + 20) ≤ KH * 2 ^ (n / 8) := hKH ▸ lin_le hH2 le_rfl hX1
  have hU := u_le l F kclk coef A a ha ha' Cs carriers translation hcall hs Cc fhn
  have pw1 : 1 ≤ 2 ^ natBitLength n := Nat.one_le_two_pow
  have pw2 : 1 ≤ 2 ^ natBitLength (ReqBridge.thrCodes Cs).length := Nat.one_le_two_pow
  have pw3 : 1 ≤ 2 ^ natBitLength (List.map Carrier.code carriers).length := Nat.one_le_two_pow
  have fcP' := fcP
  rw [pow_succ, pow_succ, pow_succ] at fcP'
  have hcp : n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2 := by omega
  have hKb : PrimT.C4GateSym.needW n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2 := by omega
  have hc := c_le l F kclk coef A a ha ha' Cs carriers translation hcall hs Fp Kc hKc Cc hcp hKb
  have hl := l_le l F kclk coef A a ha ha' Cs carriers translation hcall hs cl (hcl n)
  have hρx := rho_le Cc n _ (fv 6)
  have hbl : (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs).length ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n) := by
    have h' := fwd
    rw [List.length_append] at h'
    omega
  have hs' := nf_le l F kclk coef A a ha ha' Cs carriers translation hcall hs ce (hce n) Cc hbl s
  have hY := y_le' _ _ ((thrReq n a' ha' Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)).length _ _ _ Cc n KH (fv 5) (fv 3) (fv 2) (fv 4) fwd hcs
  have hk : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n / 16 + K0 := le_trans (PrimT.C4SymN.kOf_le_bsq l F kclk coef A a ha n) (hK0 n)
  have hkn : (((gate0 l F).budget kclk coef A a ha).kOf n) ≤ n := ((callInputs l F kclk coef A a ha).starParams n hs).k_le_n
  have hlin := lin_ell l F kclk coef A a ha ha' Cs carriers translation hcall hs Kq (hKq n)
  have hd2 : (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs)) ≤ n - (((gate0 l F).budget kclk coef A a ha).kOf n) + 1 := d2_le _
  have hK2 : n + 1 ≤ 2 ^ (n / 8 + c1) := by
    have q := hc1 n
    unfold Ex at q
    rw [pow_one, one_mul] at q
    exact q
  rw [thrB_split]
  exact thr_steps_core E₄ EW L _ n CL Cd Cc _ _ _ _ _ _ _ _ _ _ _ _ Fm cW Kp Dp K0 K1 c1 _ _ _ _ _ _ (Kq + 1)
    _ _ _ hcell hb hF hN hH hU hc hl hρx hs' hY (le_trans (by norm_num) hn) hk hkn hlin hd2
    (hpad kclk coef A a ha n a' ha' Cs carriers translation hcall hs) (hK1 n) hK2 le_rfl hEc hEa hAt

end NearCubicWires.WireExponent3_5.PrimAsm.ThrBud

end
