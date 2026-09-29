import Proof.Wire_3_5.Primitive.SeedFix.FlipsSetup
import Proof.Wire_3_5.Primitive.SeedFix.NwB13

/-! # NW phase (b), part 14: the constants of phase (b)'s term

From `NeedB l` (the output machine: every number phase (b)'s registers hold is at most `K_n(F)·X^{D_n(f_e)}`, `X = |fpIn| + 1`):
**`KbB`**, **`DbB`** (the capacity's coefficient and exponent: `64(U+1)²·(X+2)^{C_sp+3} ≤ K_b·X^{D_b}` with
`U = K_n X^{D_n} + X + c_F`, **`cap_le`**), and **`capNeed_mono`**.

Paper quantity of the main types: phase (b)'s capacity, polynomial in the input (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

theorem capNeed_mono {C : Ledger.CapParams} {m : Mode} {q r s c c' : ℕ} (h : SymDec.CapNeed C m q r s c)
    (hc : c ≤ c') : SymDec.CapNeed C m q r s c' :=
  ⟨by have := h.hc1; omega, by have := h.hr; omega, by have := h.hs; omega, by have := h.hq; omega,
    by have := h.hL1; omega, by have := h.h48; omega, by have := h.h32; omega, by have := h.h64; omega,
    by have := h.h4832; omega, by have := h.hrsq; omega, by have := h.hC; omega, by have := h.hnum; omega,
    by have := h.hLK; omega, by have := h.hsum; omega, by have := h.hroot1; omega, by have := h.h3; omega,
    by have := h.h3q; omega, by have := h.hCe; omega, by have := h.hE; omega, by have := h.hroot2; omega⟩

section Consts
variable (l : Literals) (hN : NeedB l)

/-- The capacity coefficient. -/
noncomputable def KnX : GateFree l → ℕ := Classical.choose hN
/-- The capacity exponent. -/
noncomputable def DnX : ℕ → ℕ := Classical.choose (Classical.choose_spec hN)

theorem atomsX (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    AtomsB l F kclk coef A a ha hs Cs carriers
      (KnX l hN F * ((FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length + 1) ^ DnX l hN F.filterErrDeg)
      (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨_, hc⟩) :=
  Classical.choose_spec (Classical.choose_spec hN) F kclk coef A a ha n a' ha' Cs carriers translation hc hs

/-- The gate's constants the programs meet (`f_e`, `c_r`, W6's `C_n`, the schedule's `J`). -/
noncomputable def cstB (F : GateFree l) : ℕ := F.filterErrDeg + F.cr + (ThrDecF.NW l).Cn + SymSizes.schedJ l + 1000

/-- **The capacity's coefficient.** -/
noncomputable def KbB (F : GateFree l) : ℕ := 64 * (KnX l hN F + cstB l F + 2) ^ 2 * 3 ^ (gateCsp l + 3)

/-- **The capacity's exponent.** -/
noncomputable def DbB (fe : ℕ) : ℕ := 2 * (DnX l hN fe + 1) + (gateCsp l + 3)

/-- **The capacity dominates** `64(U+1)²·(X+2)^{C_sp+3}`. -/
theorem cap_le (F : GateFree l) (X : ℕ) (hX : 1 ≤ X) :
    64 * ((KnX l hN F * X ^ DnX l hN F.filterErrDeg + X + cstB l F) + 1) ^ 2 * (X + 2) ^ (gateCsp l + 3) ≤
      KbB l hN F * X ^ DbB l hN F.filterErrDeg := by
  obtain ⟨K, hK⟩ : ∃ K, K = KnX l hN F := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = DnX l hN F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = cstB l F := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = gateCsp l + 3 := ⟨_, rfl⟩
  have hXD : X ^ D ≤ X ^ (D + 1) := Nat.pow_le_pow_right hX (by omega)
  have hX1 : X ≤ X ^ (D + 1) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (D + 1) := Nat.pow_le_pow_right hX (by omega)
  have hP1 : 1 ≤ X ^ (D + 1) := Nat.one_le_pow _ _ (by omega)
  have hU : K * X ^ D + X + s + 1 ≤ (K + s + 2) * X ^ (D + 1) := by
    have a1 : K * X ^ D ≤ K * X ^ (D + 1) := Nat.mul_le_mul_left _ hXD
    have a2 : s + 1 ≤ (s + 1) * X ^ (D + 1) := Nat.le_mul_of_pos_right _ hP1
    have e : (K + s + 2) * X ^ (D + 1) = K * X ^ (D + 1) + X ^ (D + 1) + (s + 1) * X ^ (D + 1) := by ring
    omega
  have hU2 : (K * X ^ D + X + s + 1) ^ 2 ≤ (K + s + 2) ^ 2 * X ^ (2 * (D + 1)) := by
    calc (K * X ^ D + X + s + 1) ^ 2 ≤ ((K + s + 2) * X ^ (D + 1)) ^ 2 := Nat.pow_le_pow_left hU 2
      _ = (K + s + 2) ^ 2 * X ^ (2 * (D + 1)) := by rw [mul_pow, ← pow_mul, mul_comm (D + 1) 2]
  have hS : (X + 2) ^ E ≤ 3 ^ E * X ^ E := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have eDb : DbB l hN F.filterErrDeg = 2 * (D + 1) + E := by rw [hD, hE]; rfl
  have eKb : KbB l hN F = 64 * (K + s + 2) ^ 2 * 3 ^ E := by rw [hK, hs, hE]; rfl
  rw [eDb, eKb, ← hK, ← hD, ← hs, ← hE]
  calc 64 * (K * X ^ D + X + s + 1) ^ 2 * (X + 2) ^ E
      ≤ 64 * ((K + s + 2) ^ 2 * X ^ (2 * (D + 1))) * (3 ^ E * X ^ E) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hU2) hS
    _ = 64 * (K + s + 2) ^ 2 * 3 ^ E * X ^ (2 * (D + 1) + E) := by rw [pow_add]; ring

end Consts

section Run2
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec
variable (x : ℕ) {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- **Phase (b)'s run**, its time bounded by `bKc·(3c₀+3)^{fD}`. -/
theorem b_run2 (hx : ThrDecF.dX T N ≤ x) (cr fe cap c₀ : ℕ) (hc₀ : c₀ ≤ cap) (P : Shared.StarParams)
    (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (cc : List ℕ) (tl : List Bool)
    (hKb : ∀ c ∈ ReqBridge.thrCodes Cs,
      natBitLength c ≤ (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length)
    (σ : WState (LNS x) LNR) (vN vM vE vT : ℕ)
    (hin : σ.st (NumsPh2.sIn x) = frame (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl))
    (hcl : ∀ i, i ≠ NumsPh2.sIn x → σ.st i = []) (hsh : ∀ i, σ.sh i = 0)
    (hN : σ.val NumsPh2.rN = vN) (hM : σ.val NumsPh2.rM = vM) (hE : σ.val NumsPh2.rE = vE)
    (hT : σ.val NumsPh2.rT = vT)
    (hz : ∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → σ.val q = 0)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : cc.length ≤ 2)
    (hB1 : 1 ≤ Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (hok : PrimThrW.TopFront2.TF2Ok Cs cc (ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn))
    (hneed : N.need (P.n + Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) ≤
      ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn)
    (cN : vN ≤ c₀) (cM : vM ≤ c₀) (cE : vE ≤ c₀) (cT : vT ≤ c₀)
    (hc1 : 2 * (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length + 2 ≤ c₀)
    (hcP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength (ReqBridge.thrCodes Cs).length + 1) +
      2 ^ (natBitLength cc.length + 1) + (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length + P.n +
      (ReqBridge.thrCodes Cs).length + 1 ≤ c₀)
    (hc3 : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ c₀)
    (hkc : P.s * (P.r / 2) ≤ c₀) (hfc : fe * Nat.clog 2 (P.n + 2) ≤ c₀)
    (hcS : 4 * P.n + 2 * cr + 20 ≤ c₀)
    (hcP' : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ c₀)
    (hcC : SymDec.CapNeed C .thr P.n (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) c₀)
    (hcA : (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length + (P.n + 1) ^ 26 * 2 + P.n +
      Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + 42 ≤ c₀)
    (hCn : N.Cn ≤ c₀)
    (hPD : (P.n + Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + 1) ^ N.Dn ≤ c₀)
    (hcB : ThrDecF.tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) N.Cn N.Dn + P.n +
      Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n + cc.length + 42 ≤ c₀)
    (cvl : ∀ i : Fin 14, (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).get i ≤ c₀)
    (hcT : Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n * 32 + 2 ≤ c₀)
    (hcN : 2 * (P.n + 1) ^ 26 + 8 ≤ c₀) (hcF : fe * Nat.clog 2 (P.n + 2) + 4 ≤ c₀)
    (hsc : 2 ^ ((SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).seedBits + 1) ≤ c₀)
    (hlc : (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).labelBits +
      (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).fieldBits +
      (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
      (fe * Nat.clog 2 (P.n + 2))).walkLen + 512 ≤ c₀)
    (hqc : 2 * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG *
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut) + 1 ≤ c₀)
    (hnp1 : 1 ≤ (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
      (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr)
    (hV : vVal (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).pSum
      (2 ^ (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
        (fe * Nat.clog 2 (P.n + 2))).seedBits)
      (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
        (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr
      P.n (P.s * (P.r / 2)) ≤ c₀)
    (J : ℕ) (hJt : Ledger.rowBt h0 h1 P.n ≤ J * c₀ + J + 1) (hsp : Ledger.rowBSparse h0 h1 2 Cδ P.n ≤ c₀)
    (hLq : Ledger.Lq P.n ≤ c₀) (hc0 : 1 ≤ c₀) :
    ∃ (τ : WState (LNS x) LNR) (m : ℕ), Step (bM x T N hx cr fe ζ Cδ C) m (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ bKc T N J * (3 * c₀ + 3) ^ ThrDecF.fD T N ∧
      τ.st (NumsPh2.sIn x) = frame (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) ∧
      τ.st (NumsPh2.sW0 x) = [] ∧ τ.st (NumsPh2.sW1 x) = [] ∧ (∀ i, τ.sh i = 0) ∧ τ.cell = σ.cell ∧
      τ.val NumsPh2.rN = vN ∧ τ.val NumsPh2.rM = vM ∧ τ.val NumsPh2.rE = vE ∧ τ.val NumsPh2.rT = vT ∧
      τ.val NumsPh2.rV = vVal (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nG
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).cut
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).pSum
          (2 ^ (SymDec.gP P.n (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
            (fe * Nat.clog 2 (P.n + 2))).seedBits)
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length
            (Ledger.rowBCap C .thr (Ledger.rowBr cr P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)).nPr
          P.n (P.s * (P.r / 2)) ∧
      (∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → q ≠ NumsPh2.rV → τ.val q = 0) := by
  obtain ⟨τ, m, hs, hm, rest⟩ := b_run x T N hx cr fe cap c₀ hc₀ P hrP h0 h1 Cδ C Cs cc tl hKb σ vN vM vE vT hin hcl hsh
    hN hM hE hT hz hn ha hd hnc hB1 hok hneed cN cM cE cT hc1 hcP hc3 hkc hfc hcS hcP' hcC hcA hCn hPD hcB cvl hcT hcN hcF
    hsc hlc hqc hnp1 hV
  have hca : (ReqBridge.thrCodes Cs).length ≤ 4 := by simp [ReqBridge.thrCodes]; exact ha
  refine ⟨τ, m, hs, le_trans hm (b_cost_le T N J c₀ vN vM vE vT P.n _ _ _ cr fe _ _ _ _ _ _ _ _ _ (by omega) (by omega)
    hca hnc (by omega) hc3 (by omega) (by omega) hc0 hJt hsp hLq (by unfold ThrDecF.tV at hcB ⊢; omega) (by omega)
    (by omega)), rest⟩

end Run2

end NearCubicWires.WireExponent3_5.PrimT.NwB
