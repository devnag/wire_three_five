import Lean
import Proof.Wire_3_5.Primitive.Writers.SymFamBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymHelp
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SymFamCostBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (SYM leaf), part 12: the SYM writer's budget in the preprocessing class

* `SB.E1`, `SB.d1`, `SB.K1` (the request side `|w| + n + cc + 2 ≤ K₁Q^{d₁}`), `SB.Ec2`, `SB.Kc2` (the dimension stage
  `c₂ ≤ K_{c2}(n+2)^{E_{c2}}`, **`c2_fam`**), **`SB.Etot`** (the budget's exponent: the producers' and the literals'
  exponents only), `SB.Ktot`, **`SB.cWr`** (the writer's coefficient, after `F`), **`SB.EW`** (`c_ψ = E_tot·c_S`);
* **`sym_fam_cost`**: `costS … ≤ c_W·classBound E_W .preprocessing n k Ψ` for every envelope with `c_ψ ≥ E_tot·c_S`
  (`costS ≤ K_tot·Q^{E_tot}`, then `SymSizes.class_linkS`); `SB.Etot_eq` (the exponent reads the exponents only).

Paper quantity of the main type: the SYM writer's running time within `2^{O(Ψ)}q^{O(1)}` (prim:runtime P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline

/-! ## The budget's class link -/

namespace SB

end SB

section CostC
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

/-- **The SYM dimension stage's cost at the family**: `c₂ ≤ K_{c2}·(n+2)^{E_{c2}}`. -/
theorem c2_fam (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (h : SB)
    (hZ : h.Z = CallIndexR.capZR l) (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l)
    (hKL : h.KLam = SymSizes.KLam l) (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) {n : ℕ}
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) :
    2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
        (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2 ≤ h.Kc2 * (n + 2) ^ h.Ec2 := by
  obtain ⟨Wv, hWv⟩ : ∃ x, x = UnaryCalc.value h.Dv h.Cv n := ⟨_, rfl⟩
  have eW : 2 ^ (h.cW + 2 * h.Dv) * (n + 1) ^ h.Dv = Wv := by rw [hWv]; rfl
  rw [← hWv]
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hLn : L ≤ n + 2 := hLd ▸ clog_le_self _
  have hB : ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n ≤ h.capK * (n + 2) ^ h.Z := by
    rw [hK, hZ]; exact sfam_capS l F kclk coef A a0 ha0 n
  -- the stage's needs at `2W + 2`
  have t1 := termY (cW := h.cW) (Dv := h.Dv) (K := 1) (c := 0) (d := 2) (n := n) (by norm_num)
    (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
  have t2 := termY (cW := h.cW) (Dv := h.Dv) (K := 2 * h.cr + 2) (d := 0) (n := n) (le_two_pow_clog _)
    (by unfold SB.cW; omega) (Nat.zero_le _)
  have t3 := termY (cW := h.cW) (Dv := h.Dv) (K := 2 ^ (1 + Nat.clog 2 (h.J + 6))) (c := 1 + Nat.clog 2 (h.J + 6))
    (d := 1) (n := n) le_rfl (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
  have t4 := termY (cW := h.cW) (Dv := h.Dv) (K := h.KLam) (d := 3) (n := n) (le_two_pow_clog _)
    (by unfold SB.cW; omega) (by unfold SB.Dv; omega)
  rw [eW, one_mul] at t1
  rw [eW, pow_zero, mul_one] at t2
  rw [eW] at t3 t4
  have q2 : n + 2 ≤ (n + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hP := ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  have hr4 : 4 * ((callInputs l F kclk coef A a0 ha0).starParams n hs).r ≤ n :=
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).four_r_le_n
  have hr2 : 2 ≤ ((callInputs l F kclk coef A a0 ha0).starParams n hs).r :=
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).two_le_r
  have hsn : ((callInputs l F kclk coef A a0 ha0).starParams n hs).s ≤ n + 1 := by
    unfold Shared.StarParams.s
    exact le_trans (Nat.log_le_self 2 _) (Nat.add_le_add_right (Nat.div_le_self _ _) 1)
  have hbn : ((callInputs l F kclk coef A a0 ha0).starParams n hs).b ≤ n :=
    le_trans (Nat.le_mul_of_pos_left _ (by omega)) ((callInputs l F kclk coef A a0 ha0).starParams n hs).r_mul_b_le
  have hkn : ((callInputs l F kclk coef A a0 ha0).starParams n hs).k ≤ (n + 2) ^ 2 := by
    unfold Shared.StarParams.k
    exact le_trans (Nat.mul_le_mul (show ((callInputs l F kclk coef A a0 ha0).starParams n hs).r ≤ n + 2 by omega)
      (show ((callInputs l F kclk coef A a0 ha0).starParams n hs).s ≤ n + 2 by omega)) (le_of_eq (by ring))
  have ht : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n + 5 ≤ 2 ^ (1 + Nat.clog 2 (h.J + 6)) * (n + 2) ^ 1 := by
    have hr := SymSizes.rowBt_le l n
    rw [← hJ, ← hLd] at hr
    exact t5_le hr hLn (le_two_pow_clog _)
  have hΛ := SymSizes.lambda_le l n
  rw [← hKL] at hΛ
  have hc := SymSizes.numsStageCostS_le (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) Wv
    ((callInputs l F kclk coef A a0 ha0).starParams n hs) 26 6 h.KF F.cr
    (by show n + 2 ≤ 2 * Wv + 2; omega) (by rw [← hcr]; omega)
    (by omega) (by omega) (by omega) (by omega)
    (by show Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n + 5 ≤ 2 * Wv + 2; omega)
    (by show Nat.clog 2 (n + 2) ≤ 2 * Wv + 2; omega)
    (by show Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n ≤ 2 * Wv + 2; omega)
  have hT := SymSizes.tS_le_poly (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) h.capK h.Z n hB
  have eKT : 32 * (196608 * (Nat.clog 2 h.capK + 23 + h.Z) * (h.capK + 1) + 1) = h.KT := rfl
  rw [eKT] at hT
  have hsp : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ (n + 2) ^ (h.Csp + 3) := by
    rw [hCsp]; exact CallIndex.sp_le l n
  have hS : CanonicalFourfoldRowProgram.natCeilSqrt (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n * 33554432) ≤
      ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n * 33554432 + 1 :=
    SymSizes.natCeilSqrt_le_of (Nat.le_trans (Nat.le_succ _) (Nat.le_mul_self _))
  exact c2_arith hc (hWv.trans (value_eq _ _ _)) hB hS hT hsp (by unfold SB.Ec2; omega) (by unfold SB.Ec2; omega)
    (by unfold SB.Ec2; omega) (by unfold SB.Ec2 SB.Dv; omega) (by unfold SB.Ec2; omega)

end CostC

section Cost2
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

/-- **The SYM writer's budget is in the preprocessing class**: `costS … ≤ c_W·classBound E_W .preprocessing n k Ψ`
at every SYM call of the family (`E_W` with `c_ψ = E_tot·c_S`, `C_D ≥ 1`). -/
theorem sym_fam_cost (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (h : SB)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hsy1 : Data.symCc = h.Csy) (hsy2 : Data.symDc = h.Dsy)
    (hZ : h.Z = CallIndexR.capZR l) (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l)
    (hKL : h.KLam = SymSizes.KLam l) (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) (hCD : 1 ≤ F.CD)
    (EW : Envelope) (hcpsi : h.Etot * SymSizes.cSOf h.Z 26 ≤ EW.cpsi) {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) :
    ShellT.costS h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA (symReq n a ha Cs carriers translation).word.length n
        (Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
        (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
          (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2)
        (UnaryCalc.value h.D h.Kr (2 ^ NumsXS.mS h.KF ((callInputs l F kclk coef A a0 ha0).starParams n hs)
          (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6) - 1)
        (NumsXS.mS h.KF ((callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l)
          (gateCδ1 l) (gateCap l) 26 6) ≤
      h.cWr * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
        (((gate0 l F).budget kclk coef A a0 ha0).psiOf n) := by
  have hwl : (symReq n a ha Cs carriers translation).word.length ≤ h.Cw * (n + 1) ^ h.Dw :=
    le_trans (CallSize.gate_word_length_le l F kclk coef A a0 ha0 _ hcall) (hwb n)
  obtain ⟨hk2, hdesc, henv⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a0 ha0 hs
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLd]; exact Nat.clog_pos (by norm_num) (by omega)
  have hn2 : n + 2 ≤ 2 ^ L := by rw [hLd]; exact Nat.le_pow_clog (by norm_num) _
  obtain ⟨BS, hBSd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n := ⟨_, rfl⟩
  have hBS : BS ≤ h.capK * (n + 2) ^ h.Z := by rw [hBSd, hK, hZ]; exact sfam_capS l F kclk coef A a0 ha0 n
  -- the dimension
  have hm := sfam_mS l F kclk coef A a0 ha0 hs h.KF
  obtain ⟨k, hkd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a0 ha0).kOf n := ⟨_, rfl⟩
  rw [← hkd, ← hLd, ← hBSd] at hm
  obtain ⟨m, hmd⟩ : ∃ x, x = NumsXS.mS h.KF ((callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l)
      (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 := ⟨_, rfl⟩
  rw [← hmd] at hm ⊢
  obtain ⟨Q, hQd⟩ : ∃ x, x = 2 ^ m + 1 := ⟨_, rfl⟩
  have hLm : L ≤ m := by rw [hm]; exact le_trans (Nat.le_add_left _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have hnQ : n + 2 ≤ Q := by
    rw [hQd]; exact le_trans hn2 (le_trans (Nat.pow_le_pow_right (by norm_num) hLm) (Nat.le_succ _))
  have hQ1 : 1 ≤ Q := le_trans (by omega) hnQ
  have qp : ∀ d d', d ≤ d' → Q ^ d ≤ Q ^ d' := fun d d' hd => Nat.pow_le_pow_right hQ1 hd
  have nq : ∀ d, (n + 1) ^ d ≤ Q ^ d := fun d => Nat.pow_le_pow_left (by omega) d
  have nq2 : ∀ d, (n + 2) ^ d ≤ Q ^ d := fun d => Nat.pow_le_pow_left hnQ d
  -- the data stage's cost
  obtain ⟨dC2, dD2⟩ := h.data_ge
  have hD21 : 1 ≤ h.D2 := by unfold SB.D2; omega
  have hn1 : 1 ≤ n + 1 := Nat.succ_pos _
  have eV : UnaryCalc.value h.D2 h.C2 n = h.C2 * (n + 1) ^ h.D2 := value_eq _ _ _
  have hnwV : PrimT.C4GateSym.needW n ≤ UnaryCalc.value h.D2 h.C2 n := by
    rw [eV]; exact le_trans (hnw n) (Nat.mul_le_mul dC2 (Nat.pow_le_pow_right hn1 dD2))
  have td := PrimT.C4GateSym.sym_data_hyps Cs carriers ha hk2 hdesc henv (UnaryCalc.value h.D2 h.C2 n) hnwV
  have hcc := Data.coreCost_poly Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n)
    (UnaryCalc.value h.D2 h.C2 n) ha hk2 td.1 td.2.1 td.2.2.2.2.2.2.2.2.2.1 td.2.2.2.2.2.2.2.2.2.2 td.2.2.1
  unfold ValidatorPolynomialDomination.PolyBounded at hcc
  rw [hsy1, hsy2] at hcc
  have hV3 : UnaryCalc.value h.D2 h.C2 n + n + UnaryCalc.value h.D2 h.C2 n + UnaryCalc.value h.D2 h.C2 n + 1 ≤
      (3 * h.C2 + 1) * (n + 1) ^ h.D2 := by
    have a1 : n + 1 ≤ (n + 1) ^ h.D2 := le_of_eq_of_le (pow_one _).symm (Nat.pow_le_pow_right hn1 hD21)
    rw [eV]
    have e : (3 * h.C2 + 1) * (n + 1) ^ h.D2 = 3 * (h.C2 * (n + 1) ^ h.D2) + (n + 1) ^ h.D2 := by ring
    omega
  have hcc2 : Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n) ≤
      h.Csy * (3 * h.C2 + 1) ^ h.Dsy * (n + 1) ^ (h.D2 * h.Dsy) := by
    have a1 := Nat.mul_le_mul_left h.Csy (Nat.pow_le_pow_left hV3 h.Dsy)
    rw [mul_pow, ← pow_mul] at a1
    have a2 := le_trans hcc a1
    calc _ ≤ h.Csy * ((3 * h.C2 + 1) ^ h.Dsy * (n + 1) ^ (h.D2 * h.Dsy)) := by omega
      _ = _ := by ring
  -- the request side `≤ K₁·Q^{d₁}`
  have hreq : (symReq n a ha Cs carriers translation).word.length + n +
      Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n) + 2 ≤ h.K1 * Q ^ h.d1 := by
    have p1 : (n + 1) ^ h.Dw ≤ Q ^ h.d1 := le_trans (nq _) (qp _ _ (by unfold SB.d1; omega))
    have p2 : (n + 1) ^ (h.D2 * h.Dsy) ≤ Q ^ h.d1 := le_trans (nq _) (qp _ _ (by unfold SB.d1; omega))
    have p3 : n + 2 ≤ Q ^ h.d1 := le_trans hnQ (le_of_eq_of_le (pow_one Q).symm (qp _ _ (by unfold SB.d1; omega)))
    have a1 : h.Cw * (n + 1) ^ h.Dw ≤ h.Cw * Q ^ h.d1 := Nat.mul_le_mul_left _ p1
    have a2 : h.Csy * (3 * h.C2 + 1) ^ h.Dsy * (n + 1) ^ (h.D2 * h.Dsy) ≤
        h.Csy * (3 * h.C2 + 1) ^ h.Dsy * Q ^ h.d1 := Nat.mul_le_mul_left _ p2
    have e : h.K1 * Q ^ h.d1 = h.Cw * Q ^ h.d1 + 2 * Q ^ h.d1 + h.Csy * (3 * h.C2 + 1) ^ h.Dsy * Q ^ h.d1 := by
      unfold SB.K1; ring
    omega
  -- the dimension stage
  have hc2 := c2_fam l F kclk coef A a0 ha0 h hZ hCsp hJ hKL hK hcr hs
  -- the budget `≤ K_tot·Q^{E_tot}`
  have hc := ShellT.costS_le h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA (symReq n a ha Cs carriers translation).word.length n
    (Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
    (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
      (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2)
    (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) m
  rw [← hQd] at hc
  have eE : ShellT.EcT h.D h.D2 h.Dv 1 = h.E1 := rfl
  rw [eE] at hc
  have f1 : ((symReq n a ha Cs carriers translation).word.length + n +
      Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n) + 2) ^ h.E1 ≤
        h.K1 ^ h.E1 * Q ^ h.Etot := by
    refine le_trans (Nat.pow_le_pow_left hreq _) ?_
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ (qp _ _ (by unfold SB.Etot; omega))
  have f2 : Q ^ h.E1 ≤ Q ^ h.Etot := qp _ _ (by unfold SB.Etot; omega)
  have eR : UnaryCalc.value h.D h.Kr (2 ^ m) = h.Kr * Q ^ h.D := by rw [value_eq, ← hQd]
  have eL : UnaryCalc.value 1 h.KA (2 ^ m) = h.KA * Q := by rw [value_eq, pow_one, ← hQd]
  have f3 : UnaryCalc.value 1 h.KA (2 ^ m) * (2 * (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) +
      2 * UnaryCalc.value h.D h.Kr (2 ^ m) + 10) ≤ h.KA * (4 * h.Kr + 10) * Q ^ h.Etot := by
    rw [eL, eR]
    have a1 : 2 * (h.Kr * Q ^ h.D - 1) + 2 * (h.Kr * Q ^ h.D) + 10 ≤ (4 * h.Kr + 10) * Q ^ h.D := by
      have : 1 ≤ Q ^ h.D := Nat.one_le_pow _ _ hQ1
      have e : (4 * h.Kr + 10) * Q ^ h.D = 4 * (h.Kr * Q ^ h.D) + 10 * Q ^ h.D := by ring
      omega
    calc h.KA * Q * (2 * (h.Kr * Q ^ h.D - 1) + 2 * (h.Kr * Q ^ h.D) + 10)
        ≤ h.KA * Q * ((4 * h.Kr + 10) * Q ^ h.D) := Nat.mul_le_mul_left _ a1
      _ = h.KA * (4 * h.Kr + 10) * Q ^ (h.D + 1) := by rw [pow_succ]; ring
      _ ≤ h.KA * (4 * h.Kr + 10) * Q ^ h.Etot := Nat.mul_le_mul_left _ (qp _ _ (by unfold SB.Etot; omega))
  have f4 : 2 * (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n)
      ((callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)
      26 6 h.KF F.cr + 2) ≤ 2 * h.Kc2 * Q ^ h.Etot := by
    have a1 := le_trans hc2 (Nat.mul_le_mul_left h.Kc2 (le_trans (nq2 _) (qp h.Ec2 h.Etot (by unfold SB.Etot; omega))))
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 a1
  have htot : ShellT.costS h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA (symReq n a ha Cs carriers translation).word.length n
      (Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
      (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
        (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2)
      (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) m ≤ h.Ktot * Q ^ h.Etot := by
    have g1 := Nat.mul_le_mul_left (ShellT.KcT h.D h.Kr h.D2 h.C2 h.Dv h.Cv 0 1 h.KA 0) f1
    have g2 := Nat.mul_le_mul_left (ShellT.KcT h.D h.Kr h.D2 h.C2 h.Dv h.Cv 0 1 h.KA 0) f2
    have e : h.Ktot * Q ^ h.Etot = ShellT.KcT h.D h.Kr h.D2 h.C2 h.Dv h.Cv 0 1 h.KA 0 * (h.K1 ^ h.E1 * Q ^ h.Etot) +
        ShellT.KcT h.D h.Kr h.D2 h.C2 h.Dv h.Cv 0 1 h.KA 0 * Q ^ h.Etot + h.KA * (4 * h.Kr + 10) * Q ^ h.Etot +
        2 * h.Kc2 * Q ^ h.Etot := by
      unfold SB.Ktot; ring
    omega
  -- the class link
  have hB' : BS ≤ h.capK * 2 ^ (h.Z * L) := by
    have : (n + 2) ^ h.Z ≤ 2 ^ (h.Z * L) := by rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left hn2 _
    exact le_trans hBS (Nat.mul_le_mul_left _ this)
  have hcl := SymSizes.class_linkS EW h.Etot h.Ktot h.KF h.Z 26 6 h.capK F.CD n k L
    (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n) BS h.Etot_pos hL1 hCD (by omega) hB' hcpsi
  rw [← hm, ← hQd] at hcl
  have ecW : h.Ktot * 2 ^ (SymSizes.cFOf h.Etot h.KF h.Z 26 6 h.capK + h.Etot) = h.cWr := rfl
  rw [ecW] at hcl
  have epsi : ((gate0 l F).budget kclk coef A a0 ha0).psiOf n = loadPsi F.CD k L
      (((gate0 l F).budget kclk coef A a0 ha0).capOf .thr n) BS := by
    rw [hkd, hLd, hBSd]; rfl
  rw [← hkd, epsi]
  exact le_trans htot hcl

end Cost2

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam

end
