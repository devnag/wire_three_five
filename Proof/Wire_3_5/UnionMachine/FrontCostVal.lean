import Lean
import Proof.Wire_3_5.UnionMachine.FrontCostC1
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.C1Ref
import Proof.Wire_3_5.UnionMachine.FrontSelReq
import Proof.Wire_3_5.UnionMachine.FrontSemCap1
import Proof.Wire_3_5.UnionMachine.FrontSemEnt
import Proof.Wire_3_5.UnionMachine.FrontSemPath
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.UnionMachine.FrontCostValBase


noncomputable section
set_option maxRecDepth 4096


/-! # C6 front, the time (7): the valid path's cost at a guess (P3:3669-3691)

**`GF_le`**, **`PF_le`** (C1's request pieces grow with the variable count), **`nV_le`** (the numbers' registers
within `Z` when the grid, the mass, the counts and the data bound are), and **`validCost_le`**: at a guess with its
capacities (`PathCaps`, `EndCaps`) and its size envelope, and `n` above the width and the machine's polynomial
budgets, the valid path costs at most `C·n^D + 400·rOf + β`, `β` C1's call's budget.

Paper quantity of the main type: the valid path's time against the input length, the loop's capacity and C1's call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostVal
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit
open NearCubicWires.RepairRepresentation (natWord natListWord)

section Pieces

end Pieces

section Regs

end Regs

section Guess
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG)
open NearCubicWires.RepairOrdinary.Streaming (marks)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **C1's carrier loop's round fuel.** -/
theorem cG_le (g : UnionGuess S z) {Λ K Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT M : ℕ} {d : ℕ}
    (c : Plan.C1At d) (hG : FrontSemCap1.GEnv g Λ K)
    (hPC : FrontSemPath.PathCaps g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb c)
    (hEC : FrontSemTW.EndCaps h0 h1 g (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV aT bT crT KT AT)
    (hr : B.rOf g.q = Ledger.rowBr cr g.q) (hVb : Vb ≤ M + 2) (h2W : 2 * (Kw * (g.q + 1) ^ Dw) + 2 ≤ M + 2)
    (hKW : 2 * (K * K * K * K) + 2 * K + 1 ≤ Kw * (g.q + 1) ^ Dw) (hBn : Kb * (g.q + 1) ^ Db ≤ M + 2) :
    FrontSemPath.cG g (Kw * (g.q + 1) ^ Dw) Vb ≤ 10 ^ 12 * (M + 2) ^ 6 := by
  have hn : 1 ≤ M + 2 := by omega
  have hq := hG.q
  have hnv : nvG g ≤ K := hG.nv
  have hcb := hG.cb
  have hcb' : g.pcpp.clauseBits ≤ K := le_trans (Nat.lt_two_pow_self (n := g.pcpp.clauseBits)).le hcb
  have hlits : (C1Ref.litsG g).length = 2 * 2 ^ g.pcpp.clauseBits := FrontTW.pairsOf_length _ _
  have e1 : 2 ^ (g.pcpp.clauseBits + 1) = 2 * 2 ^ g.pcpp.clauseBits := by rw [pow_succ]; ring
  have hsel := C1Ref.reqWord_selWord g cr hr
  have hc2 := hPC.cap2
  rw [FrontSemCap1.frame_len] at hc2
  have hsw : (C1Asm.reqWord g.q (Ledger.rowBr cr g.q) (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (C1Ref.VG g))
      (C1Gates.npF (C1Ref.litsG g) (C1Ref.VG g)) (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (C1Ref.VG g))
      (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (C1Ref.VG g))).length ≤ M + 2 := by
    rw [hsel]; omega
  unfold C1Asm.reqWord at hsw
  simp only [List.length_append] at hsw
  have hB := hEC.bnd.cr
  have hK4 : K ≤ Kw * (g.q + 1) ^ Dw := by omega
  have a1 : Kw * (g.q + 1) ^ Dw ≤ M + 2 := by omega
  have a3 : nvG g ≤ M + 2 := by omega
  have a4 : g.q ≤ M + 2 := by omega
  have a5 : (C1Ref.litsG g).length ≤ M + 2 := by omega
  have a6 : g.pcpp.clauseBits ≤ M + 2 := by omega
  have a7 : 2 ^ (g.pcpp.clauseBits + 1) ≤ M + 2 := by omega
  have hGFn : (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (C1Ref.VG g)).length ≤ M + 2 := by omega
  have hPFn : (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (C1Ref.VG g)).length ≤ M + 2 := by omega
  have hB := hEC.bnd.cr
  have hws : (FrontTWKit.frItems ((List.range (foldOf (g.checkData g.translation)).nv).map
      (foldOf (g.checkData g.translation)).cw)).length ≤ M + 2 := le_trans hB hBn
  clear hsel hc2 hsw hlits e1 hB
  unfold FrontSemPath.cG
  refine FrontSemFold.supR_le _ _ _ (fun x hx => ?_)
  have hR := (hPC.capR x hx).trans h2W
  have hH := hPC.Hd x hx
  have hGF := (GF_le (C1Ref.CsG g) (C1Ref.litsG g) (show x ≤ C1Ref.VG g from le_of_lt hx)).trans hGFn
  have hPF := (PF_le (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (show x ≤ C1Ref.VG g from le_of_lt hx)).trans hPFn
  have hpre : C1CarPre.carPreCost (C1Ref.CsG g x) 0 0 ≤ M + 2 :=
    le_trans (le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hH)) a1
  have hx' : x ≤ M + 2 := by omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := capR_parts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR
  exact FrontCostC1.rcost_le (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g) (Kw * (g.q + 1) ^ Dw) Vb _ x (M + 2)
    hn a1 hVb hx' a3 a4 a5 a6 a7 hws hpre hGF r1 r2 r3 r4 r5 hPF r6 r7 r8

/-- **C1's request pieces** within the capacity. -/
theorem req_parts (g : UnionGuess S z) {Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb : ℕ} {d : ℕ} (c : Plan.C1At d)
    (hPC : FrontSemPath.PathCaps g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb c)
    (hr : B.rOf g.q = Ledger.rowBr cr g.q) :
    (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g)).length ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2 ∧
      (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g)).length ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2 := by
  have hsel := C1Ref.reqWord_selWord g cr hr
  have hc2 := hPC.cap2
  rw [FrontSemCap1.frame_len] at hc2
  have hsw : (C1Asm.reqWord g.q (Ledger.rowBr cr g.q) (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (C1Ref.VG g))
      (C1Gates.npF (C1Ref.litsG g) (C1Ref.VG g)) (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (C1Ref.VG g))
      (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (C1Ref.VG g))).length ≤
        2 * (Kw * (g.q + 1) ^ Dw) + 2 := by
    rw [hsel]; omega
  unfold C1Asm.reqWord at hsw
  simp only [List.length_append] at hsw
  have hGF : (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (C1Ref.VG g)).length ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2 := by
    omega
  have hPF : (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (C1Ref.VG g)).length ≤
      2 * (Kw * (g.q + 1) ^ Dw) + 2 := by
    omega
  exact ⟨hGF, hPF⟩

/-- **The valid path's cost**: at most `10^81·n^40 + 400·rOf + β` at `n = N + 2`, `β` C1's call's budget. -/
theorem validCost_le (g : UnionGuess S z) {Λ K Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT M : ℕ}
    {d : ℕ} (c : Plan.C1At d) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g)) (xs : List Bool)
    (k : ℕ) (hG : FrontSemCap1.GEnv g Λ K)
    (hPC : FrontSemPath.PathCaps g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb c)
    (hEC : FrontSemTW.EndCaps h0 h1 g (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV aT bT crT KT AT)
    (hr : B.rOf g.q = Ledger.rowBr cr g.q) (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q)
    (hΛ : Ledger.rowBLambda h0 h1 2 g.q ≤ K) (hx : xs.length ≤ M)
    (hk : (FrontTW.entsW (FrontSemEnt.esOf g)).length + k ≤ M) (hVb : Vb ≤ M + 2)
    (h2W : 2 * (Kw * (g.q + 1) ^ Dw) + 2 ≤ M + 2) (hKW : 2 * (K * K * K * K) + 2 * K + 1 ≤ Kw * (g.q + 1) ^ Dw)
    (hDb : Db ≤ M + 2) (hP1 : RepairOrdinary.PCPSerializerCapacity.Power.budget Dw Kw g.q ≤ M + 2)
    (hP2 : RepairOrdinary.PCPSerializerCapacity.Power.budget Dl 1 g.q ≤ M + 2)
    (hP3 : RepairOrdinary.PCPSerializerCapacity.Power.budget I.carrierDeg 1 g.q ≤ M + 2)
    (hP4 : RepairOrdinary.PCPSerializerCapacity.Power.budget De Ce (Kw * (g.q + 1) ^ Dw) ≤ M + 2)
    (hP5 : RepairOrdinary.PCPSerializerCapacity.Power.budget Dt Ct (Kw * (g.q + 1) ^ Dw) ≤ M + 2)
    (hv : value Dt Ct (Kw * (g.q + 1) ^ Dw) ≤ M + 2) (hL : (g.q + 1) ^ Dl ≤ M + 2)
    (ht : Ledger.rowBt h0 h1 g.q ≤ M + 2) :
    FrontSemPath.validCost g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c hpre xs k ≤
      10 ^ 81 * (M + 2) ^ 40 + 400 * FrontTail.rOf crT KT AT g.q +
        (Plan.c1sized d c.E₁ c.c₁).budget ⟨FrontSelReq.selReqOf g, hpre⟩ := by
  have hn : 1 ≤ M + 2 := by omega
  have eV : nvG g = g.pcpp.systematicBits + g.pcpp.auxiliaryBits := rfl
  have hq := hG.q
  have hq2 := hG.q2
  have hnv : nvG g ≤ K := hG.nv
  have hcb := hG.cb
  have hcb' : g.pcpp.clauseBits ≤ K := le_trans (Nat.lt_two_pow_self (n := g.pcpp.clauseBits)).le hcb
  have hs := hG.s
  have hK4 : K ≤ Kw * (g.q + 1) ^ Dw := by omega
  have hB1 := hEC.hB1
  have hBn : Kb * (g.q + 1) ^ Db ≤ M + 2 := by omega
  have hsK : Ledger.rowBSparse h0 h1 2 Cδ g.q ≤ K := hsS ▸ hs
  have hEn : (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q ≤ M + 2 := by
    have h : (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * g.s + 1 ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2 := hEC.var
    rw [hsS] at h
    omega
  have hrl : (FrontTW.entsW (FrontSemEnt.esOf g) ++ List.replicate k false).length ≤ M := by
    rw [List.length_append, List.length_replicate]; exact hk
  -- the chain's front pieces
  have b1 := FrontCostRest.ch3Cost_le h0 h1 Dw Kw Dl Kb Db Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits
    g.pcpp.clauseBits M xs (FrontTW.entsW (FrontSemEnt.esOf g) ++ List.replicate k false) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hBn hDb hP1 hP2 (by omega) ht
  have b2 := FrontCostRest.atCost_le g.mode (FrontTW.entsW (FrontSemEnt.esOf g) ++ List.replicate k false) xs g.q
    ((g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q) ((g.q + 1) ^ Dl) M hrl hx
    (by omega) hEn hL
  -- phase 5
  have hWn : FrontSemPath.WnG g ≤ M + 2 := by
    have h := hPC.capC
    have h' : 2 * (Ledger.rowBSparse h0 h1 2 Cδ g.q * FrontSemPath.WnG g) + 2 * FrontSemPath.WnG g + 3 ≤
        (nvG g + 1) * (2 * (Ledger.rowBSparse h0 h1 2 Cδ g.q * FrontSemPath.WnG g) + 2 * FrontSemPath.WnG g + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hcw : (CWConst.constWord g.mode).length ≤ M + 2 := by
    have := hG.cst
    unfold CWConst.constWord
    rw [FrontSemCap1.frame_len]
    omega
  have hZ0 := hPC.Z0
  have hcwT := hPC.cwT
  have b3 := FrontCostRest.ch5Cost_le g.mode (Kw * (g.q + 1) ^ Dw)
    (FrontTW.entsW (FrontSemEnt.esOf g) ++ List.replicate k false).length (Ledger.rowBSparse h0 h1 2 Cδ g.q)
    (FrontSemPath.WnG g) (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) g.q g.pcpp.systematicBits
    g.pcpp.auxiliaryBits g.pcpp.clauseBits (Kw * (g.q + 1) ^ Dw) I.carrierDeg De Ce Dt Ct
    (foldOf (g.checkData g.translation)).nv (FrontSemPath.cwG g (value De Ce (Kw * (g.q + 1) ^ Dw))) M
    (by omega) (by omega) (by omega) hWn (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcw
    hP3 hP4 hP5 hv (by omega) (by omega)
  -- C1's call
  have hcG := cG_le h0 h1 g c hG hPC hEC hr hVb h2W hKW hBn
  have hnvn : nvG g ≤ M + 2 := by omega
  have b4 := mulc_le _ _ _ hn hnvn hcG
  obtain ⟨hGF, hPF⟩ := req_parts h0 h1 g c hPC hr
  have hc1 := hPC.cap1
  have hc2 := hPC.cap2
  rw [FrontSemCap1.frame_len] at hc2
  have b5 := FrontCostC1.asmCost_le cr g.q (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g))
    (C1Gates.npF (C1Ref.litsG g) (nvG g)) (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g))
    (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g)) (M + 2) hn (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hcC := hPC.capC1
  have b6 := FrontCostC1.convCost_le (SelectionMachine.selArgmin (FrontSelReq.selReqOf g)) (M + 2) hn (by omega)
    (by omega)
  -- the end
  have hlits : ∀ x ∈ FrontTW.litsD (g.checkData g.translation), x ≤ M + 2 := by
    intro x hx'
    have h := hEC.rdc x hx'
    have h2 := CompilerMachine.Pool.lt_pow_natBitLength x
    rw [pow_succ] at h
    omega
  have hnV := nV_le h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits K (M + 2)
    hq (by omega) (by omega) hcb hsK hΛ hBn (by omega)
  have b7 := FrontCostTW.twCost_le hn (Kb * (g.q + 1) ^ Db)
    (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
    (FrontTW.litsD (g.checkData g.translation)) hBn hnV hlits g.pcpp.clauseBits (by omega)
  have b8 := FrontCostEnd.pwCost_le h0 h1 (Kw * (g.q + 1) ^ Dw) Kb Db aV bV aT bT g.q g.pcpp.systematicBits
    g.pcpp.auxiliaryBits g.pcpp.clauseBits
    (FrontSemTW.twCost (Kb * (g.q + 1) ^ Db)
      (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
      (FrontTW.litsD (g.checkData g.translation)) g.pcpp.clauseBits) (M + 2) hn (by omega) (by omega) (by omega)
    (by omega) (by omega) hBn hDb ht
  have hAT : AT ≤ M + 2 := by
    have h := hEC.capW
    have h2 : 2 ^ AT ≤ (g.q + 1) ^ AT := Nat.pow_le_pow_left (by omega) AT
    have h3 : (g.q + 1) ^ AT ≤ KT * (g.q + 1) ^ AT := Nat.le_mul_of_pos_left _ hEC.hKT
    have h4 := Nat.lt_two_pow_self (n := AT)
    omega
  have hcT : (g.q + 1) ^ AT * KT ≤ M + 2 := by
    have h := hEC.capW
    rw [Nat.mul_comm] at h
    omega
  have hLw : (FrontSemTW.twWords (g.checkData g.translation) ++ [false]).length ≤ M + 2 := by
    have h := hEC.tw
    rw [List.length_append, List.length_singleton]
    omega
  have b9 := FrontCostEnd.endCost_le (Kw * (g.q + 1) ^ Dw)
    (FrontPw.pwCost (2 * (Kw * (g.q + 1) ^ Dw) + 2) h0 h1 Kb Db aV bV aT bT g.q g.pcpp.systematicBits
      g.pcpp.auxiliaryBits g.pcpp.clauseBits (FrontSemTW.twCost (Kb * (g.q + 1) ^ Db)
        (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
        (FrontTW.litsD (g.checkData g.translation)) g.pcpp.clauseBits))
    crT KT AT g.q (FrontSemTW.twWords (g.checkData g.translation) ++ [false]).length (M + 2) hn (by omega)
    (by omega) hLw hAT hEC.hKT hcT
  -- the powers
  have p1 : M + 2 ≤ (M + 2) ^ 40 := Nat.le_self_pow (by norm_num) _
  have p2 : (M + 2) ^ 2 ≤ (M + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  have p3 : (M + 2) ^ 3 ≤ (M + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  have p4 : (M + 2) ^ 4 ≤ (M + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  have p6 : (M + 2) ^ 6 ≤ (M + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  have p12 : (M + 2) ^ 12 ≤ (M + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  have p28 : (M + 2) ^ 28 ≤ (M + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  clear hcG hnV hlits hPC hEC hG
  unfold FrontSemPath.validCost FrontC1D.c1Cost FrontC1D.c1LocCost
  dsimp only
  omega

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostVal

end
