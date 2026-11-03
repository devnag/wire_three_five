import Lean
import Proof.Wire_3_5.Primitive.SeedFix.NwB14
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.S5TJoin2
import Proof.Wire_3_5.FinalPass.S5TNum3
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.GeoPack
import Proof.Wire_3_5.Primitive.SeedFix.NwBT
import Proof.Wire_3_5.Primitive.SeedFix.TS4K
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.Primitive.SeedFix.NwB15Base


noncomputable section
set_option maxRecDepth 120000


/-! # T3 NW phase (b), part 15: **the phase-(b) term** `phB x l hx hV hN : NumsPh3.PhB x l`

At a THR request of a call on the star, from (c)'s exit (`AfterC`): the machine `bM` at the gate's constants runs the
register programs at the virtual capacity `c₀ = K_b(F)·X^{D_b(f_e)} ≤ cap` (every need from X6's `NeedB` atoms,
`cap_le`), the docks at `cap`, within `C_s(F)·X^{D_s(f_e)}` (`b_cost_le`), and exits at `AfterV` with
`rV = vB = vOf` (X6's `VLinkB`), the word streams blank, every head `0`, the residue by the step count
(`Shell.Step.len`).

Paper quantity of the main type: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` at the THR
requests (P3:3044-3048), in time polynomial in the input (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

section Term
variable (x : ℕ) (l : Literals) (hx : ThrDecF.dX (ThrDecF.TW l) (ThrDecF.NW l) ≤ x) (hN : NeedB l)

/-- The machine at a gate. -/
noncomputable def bMF (F : GateFree l) :=
  bM x (ThrDecF.TW l) (ThrDecF.NW l) hx F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)

/-- **The time's coefficient.** -/
noncomputable def CsB (F : GateFree l) : ℕ :=
  bKc (ThrDecF.TW l) (ThrDecF.NW l) (SymSizes.schedJ l) * (6 * KbB l hN F) ^ ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l)

/-- **The time's exponent.** -/
noncomputable def DsB (fe : ℕ) : ℕ := DbB l hN fe * ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l)

theorem run_b (hV : VLinkB l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FinalPass.PlanFP.FReq l F kclk coef A a ha) (cap : ℕ) (hmode : r.1.mode = .thr)
    (hcap : KbB l hN F * ((FinalPass.PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ DbB l hN F.filterErrDeg ≤ cap)
    (σ : UnionMachine.NumsPh2.St x) (hC : UnionMachine.NumsPh3.AfterC x l F kclk coef A a ha r σ) :
    ∃ (τ : UnionMachine.NumsPh2.St x) (m : ℕ),
      m ≤ CsB l hN F * ((FinalPass.PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ DsB l hN F.filterErrDeg ∧
      Step (bMF x l hx F) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      UnionMachine.NumsPh3.AfterV x l F kclk coef A a ha r
        (CsB l hN F * ((FinalPass.PlanFP.fpIn l F kclk coef A a ha r).length + 1) ^ DsB l hN F.filterErrDeg) τ := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  have hm' : mode = .thr := hmode
  subst hm'
  obtain ⟨hk2, hd, he, hs⟩ := FinalPass.S5T.call_facts l F kclk coef A a ha ha' Cs carriers translation hc
  have hn1 := FinalPass.S5T.one_le_n l F kclk coef A a ha hs
  have hfp := FinalPass.S5T.fpIn_thr l F kclk coef A a ha n a' ha' carriers translation Cs hc
  have hnu := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A) (a := a)
    (ha := ha) ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hc⟩
  have At := atomsX l hN F kclk coef A a ha n a' ha' Cs carriers translation hc hs
  obtain ⟨tl, htl⟩ : ∃ t, t = RepairRepresentation.natListWord translation ++
      seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩ :=
    ⟨_, rfl⟩
  rw [← htl] at hfp
  -- the numbers
  obtain ⟨X, hXd⟩ : ∃ X, X = (FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length + 1 := ⟨_, rfl⟩
  rw [← hXd] at hcap At ⊢
  have hXw : (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length + 1 = X := by
    rw [hXd, hfp]
  obtain ⟨c, hcd⟩ : ∃ c, c = KnX l hN F * X ^ DnX l hN F.filterErrDeg := ⟨_, rfl⟩
  rw [← hcd] at At
  obtain ⟨c₀, hc₀d⟩ : ∃ c, c = KbB l hN F * X ^ DbB l hN F.filterErrDeg := ⟨_, rfl⟩
  rw [← hc₀d] at hcap
  have hX1 : 1 ≤ X := by omega
  have hbig := cap_le l hN F X hX1
  rw [← hcd, ← hc₀d] at hbig
  obtain ⟨U, hUd⟩ : ∃ U, U = c + X + cstB l F := ⟨_, rfl⟩
  rw [← hUd] at hbig
  obtain ⟨S, hSd⟩ : ∃ S, S = (X + 2) ^ (gateCsp l + 3) := ⟨_, rfl⟩
  rw [← hSd] at hbig
  have hS1 : 1 ≤ S := by rw [hSd]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = (U + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hQd] at hbig
  have hM1 : 1 ≤ 64 * Q := by have := Nat.one_le_pow 2 (U + 1) (by omega); omega
  have hMc : 64 * Q ≤ c₀ := le_trans (Nat.le_mul_of_pos_right _ hS1) hbig
  have hSc : S ≤ c₀ := le_trans (Nat.le_mul_of_pos_left _ hM1) hbig
  have hUU : U * U ≤ Q := by rw [hQd]; nlinarith
  have hU1 : U + 1 ≤ Q := by rw [hQd]; nlinarith
  have hcs : cstB l F = F.filterErrDeg + F.cr + (ThrDecF.NW l).Cn + SymSizes.schedJ l + 1000 := rfl
  have hcU : c ≤ U := by omega
  have hXU : X + 1000 ≤ U := by omega
  have hfU : F.filterErrDeg + 1000 ≤ U := by omega
  have hrU : F.cr + 1000 ≤ U := by omega
  have hCnU : (ThrDecF.NW l).Cn ≤ U := by omega
  have hJU : SymSizes.schedJ l ≤ U := by omega
  have hnu' : n ≤ (FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length := hnu
  have hnX : n + 1 ≤ X := by rw [hXd]; omega
  have hc0 : 1 ≤ c₀ := by omega
  have hUc : U + 1000 ≤ c₀ := le_trans (by omega : U + 1000 ≤ 64 * Q) hMc
  have hUUc : U * U + 60 * U + 60 ≤ c₀ := le_trans (by omega : U * U + 60 * U + 60 ≤ 64 * Q) hMc
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  have hcc : (carriers.map Stars.Carrier.code).length = carriers.length := by simp
  -- the request's codes inside the word
  have hKb : ∀ c' ∈ ReqBridge.thrCodes Cs,
      natBitLength c' ≤ (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length := by
    intro c' hc'
    have h1 := (ThrDecF.natWord_le_reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).1 c' hc'
    rw [Bindings.Williams14.natWord_length] at h1
    omega
  -- the atoms
  have aN := At.need
  have aT := At.capT
  have a26 := At.n26
  have aP := At.pow
  have aG := At.gap
  have aV := At.val
  have aF := At.tf
  have g0 : (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 carriers.length (TS4.capTL l F.cr n)).nG ≤ c := At.vals 0
  have g2 : (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 carriers.length (TS4.capTL l F.cr n)).cut ≤ c := At.vals 2
  have hP0 := TS4.p0need_of l F.cr n c a' carriers.length ha' hk2 (by omega)
  have h2c : 2 * c + 2 ≤ c₀ := by omega
  -- the register programs' needs at `c₀`
  have cN : n ≤ c₀ := by omega
  have hmO : UnionMachine.NumsPh2.mOf l F kclk coef A a ha ⟨_, hc⟩ ≤ c₀ := by
    have : UnionMachine.NumsPh2.mOf l F kclk coef A a ha ⟨_, hc⟩ = 1 := rfl
    omega
  have heO : UnionMachine.NumsPh2.eOf l F kclk coef A a ha ⟨_, hc⟩ ≤ c₀ :=
    le_trans (Nat.sub_le _ _) cN
  have hTf : FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨_, hc⟩ ≤ c₀ := by omega
  have hc1 : 2 * (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length + 2 ≤ c₀ := by
    omega
  have hcP : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength (ReqBridge.thrCodes Cs).length + 1) +
      2 ^ (natBitLength (carriers.map Stars.Carrier.code).length + 1) +
      (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length + n +
      (ReqBridge.thrCodes Cs).length + 1 ≤ c₀ := by
    have p1 := PrimT.W6.pow_nbl n
    have p2 := PrimT.W6.pow_nbl (ReqBridge.thrCodes Cs).length
    have p3 := PrimT.W6.pow_nbl (carriers.map Stars.Carrier.code).length
    rw [hcl] at p2 ⊢
    rw [hcc] at p3 ⊢
    omega
  have hc3 : (F.filterErrDeg + 4) * (n + 3) + 2 * F.cr + 20 ≤ c₀ := by
    have := Nat.mul_le_mul (show F.filterErrDeg + 4 ≤ U by omega) (show n + 3 ≤ U by omega)
    omega
  have hkc : ((callInputs l F kclk coef A a ha).starParams n hs).s *
      (((callInputs l F kclk coef A a ha).starParams n hs).r / 2) ≤ c₀ := by
    have := PrimT.Flips.kh_le ((callInputs l F kclk coef A a ha).starParams n hs)
    have hPn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
    omega
  have hclog : Nat.clog 2 (n + 2) ≤ n + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hfL : F.filterErrDeg * Nat.clog 2 (n + 2) ≤ U * U := Nat.mul_le_mul (by omega) (by omega)
  have hfc : F.filterErrDeg * Nat.clog 2 (n + 2) ≤ c₀ := by omega
  have hcS : 4 * n + 2 * F.cr + 20 ≤ c₀ := by omega
  have hcA : (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length + (n + 1) ^ 26 * 2 +
      n + TS4.capTL l F.cr n + 42 ≤ c₀ := by omega
  have hCn : (ThrDecF.NW l).Cn ≤ c₀ := by omega
  have hPD : (n + TS4.capTL l F.cr n + 1) ^ (ThrDecF.NW l).Dn ≤ c₀ := by omega
  have hcB : ThrDecF.tV (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length n
      (TS4.capTL l F.cr n) (ThrDecF.NW l).Cn (ThrDecF.NW l).Dn + n + TS4.capTL l F.cr n +
      (carriers.map Stars.Carrier.code).length + 42 ≤ c₀ := by
    unfold ThrDecF.tV
    rw [hcc]
    have hl : (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl).length + 1000 ≤ U := by
      omega
    have hn' : n + 1000 ≤ U := by omega
    exact tv_aux _ _ _ _ _ _ U c₀ c hl a26 hn' aT hk2 (Nat.mul_le_mul (le_trans aP hcU) hCnU) hcU hUUc
  have cvl : ∀ i : Fin 14, (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).get i ≤ c₀ := fun i => by
    rw [hcc]; exact le_trans (At.vals i) (by omega)
  have hcT : TS4.capTL l F.cr n * 32 + 2 ≤ c₀ := by omega
  have hcN : 2 * (n + 1) ^ 26 + 8 ≤ c₀ := by omega
  have hcF : F.filterErrDeg * Nat.clog 2 (n + 2) + 4 ≤ c₀ := by omega
  have aG' := le_trans (add4 _ _ _ _) aG
  have hsc : 2 ^ ((gapB l F n).seedBits + 1) ≤ c₀ := le_trans (le_trans (add4' _ _ _ _) aG) (by omega)
  have hlc : (gapB l F n).labelBits + (gapB l F n).fieldBits + (gapB l F n).walkLen + 512 ≤ c₀ := by omega
  have hqc : 2 * ((PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).nG *
      (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).cut) + 1 ≤ c₀ := by
    rw [hcc]
    have := Nat.mul_le_mul (le_trans g0 hcU) (le_trans g2 hcU)
    omega
  have hnp1 : 1 ≤ (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).nPr := by
    rw [hcc]; exact At.np
  have hVb : vVal (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).nG
      (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).cut
      (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).pSum
      (2 ^ (gapB l F n).seedBits)
      (PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
        (PrimT.W6.litAlg l) 1 (carriers.map Stars.Carrier.code).length (TS4.capTL l F.cr n)).nPr
      n (khB l F kclk coef A a ha hs) ≤ c₀ := by
    rw [hcc]; exact le_trans aV (by omega)
  have hJt : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n ≤ SymSizes.schedJ l * c₀ + SymSizes.schedJ l + 1 := by
    have := TS4.rowBt_B l n c₀ (by omega)
    omega
  have hsp : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ c₀ := by
    have h1 := PrimAsm.CallIndex.sp_le l n
    have h2 : (n + 2) ^ (gateCsp l + 3) ≤ S := by rw [hSd]; exact Nat.pow_le_pow_left (by omega) _
    exact le_trans h1 (le_trans h2 hSc)
  have hLq : Ledger.Lq n ≤ c₀ := by have := PrimAsm.CallIndex.Lq_le_N n; omega
  -- the run
  obtain ⟨τ, m, hstep, hmle, tIn, tW0, tW1, tsh, tcl, tN, tM, tE, tT, tVv, tz⟩ :=
    b_run2 x (ThrDecF.TW l) (ThrDecF.NW l) hx F.cr F.filterErrDeg cap c₀ hcap
      ((callInputs l F kclk coef A a ha).starParams n hs) (PrimT.GeoPack.starParams_r l F kclk coef A a ha n hs)
      (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) Cs (carriers.map Stars.Carrier.code) tl hKb σ n
      (UnionMachine.NumsPh2.mOf l F kclk coef A a ha ⟨_, hc⟩) (UnionMachine.NumsPh2.eOf l F kclk coef A a ha ⟨_, hc⟩)
      (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨_, hc⟩)
      (by rw [hC.hin, hfp]; exact rfl) hC.clean hC.heads hC.hn hC.hm hC.he hC.ht hC.regs hn1 ha' hd
      (by rw [hcc]; exact hk2)
      (TS4.capTL_pos l F.cr n) (ThrDecF.tf2ok_tV Cs _ tl ha' (by rw [hcc]; exact hk2) _ _ _)
      (ThrDecF.need_le_tV _ _ _ _) cN hmO heO hTf hc1 hcP hc3 hkc hfc hcS (le_trans hP0.hcP h2c)
      (capNeed_mono hP0.hcC h2c) hcA hCn hPD hcB cvl hcT hcN hcF hsc hlc hqc hnp1 hVb (SymSizes.schedJ l) hJt hsp
      hLq hc0
  have hpow : (3 * c₀ + 3) ^ ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l) ≤
      (6 * KbB l hN F) ^ ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l) * X ^ DsB l hN F.filterErrDeg := by
    have h1 : 3 * c₀ + 3 ≤ 6 * KbB l hN F * X ^ DbB l hN F.filterErrDeg := by
      rw [mul_assoc, ← hc₀d]; omega
    calc (3 * c₀ + 3) ^ ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l)
        ≤ (6 * KbB l hN F * X ^ DbB l hN F.filterErrDeg) ^ ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l) :=
          Nat.pow_le_pow_left h1 _
      _ = _ := by unfold DsB; rw [mul_pow, ← pow_mul]
  have hmB : m ≤ CsB l hN F * X ^ DsB l hN F.filterErrDeg := by
    have e : CsB l hN F * X ^ DsB l hN F.filterErrDeg = bKc (ThrDecF.TW l) (ThrDecF.NW l) (SymSizes.schedJ l) *
        ((6 * KbB l hN F) ^ ThrDecF.fD (ThrDecF.TW l) (ThrDecF.NW l) * X ^ DsB l hN F.filterErrDeg) := by
      unfold CsB; ring
    rw [e]
    exact le_trans hmle (Nat.mul_le_mul_left _ hpow)
  refine ⟨τ, m, hmB, hstep, ⟨by rw [hfp]; exact tIn, tW0, tW1, tsh, by rw [tcl]; exact hC.cell, ?_, tN, tM, tE, tT,
    ?_, tz⟩⟩
  · intro i h1 h2 h3
    have hl := Shell.Step.len hstep (sTape i) 0 (by rw [wenc_H_s, hC.heads]) (by rw [wenc_A_s, hC.clean i h1]; rfl)
    rw [wenc_A_s] at hl
    omega
  · rw [tVv]
    simp only [List.length_map]
    exact hV F kclk coef A a ha n a' ha' Cs carriers translation hc hs

/-- **The phase-(b) term** (the `NumsPh3.PhB x l`) from X6's `VLinkB l` and `NeedB l`. -/
noncomputable def phB (hV : VLinkB l) : UnionMachine.NumsPh3.PhB x l where
  s := _
  M := bMF x l hx
  Kn := KbB l hN
  Dn := DbB l hN
  Cs := CsB l hN
  Ds := DsB l hN
  run := fun F kclk coef A a ha r cap hmode hcap σ hC => by
    obtain ⟨τ, m, hm, hstep, hA⟩ := run_b x l hx hN hV F kclk coef A a ha r cap hmode hcap σ hC
    exact ⟨τ, m, hm, hstep, hA⟩

end Term

end NearCubicWires.WireExponent3_5.PrimT.NwB

end
