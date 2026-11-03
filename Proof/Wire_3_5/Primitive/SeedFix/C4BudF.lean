import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4BudE
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4BudEBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K item (h), part 6: `sym_steps_le` generic in the free program (for contract v7)

P3:3098-3100, 3105-3115: the `sym_steps_le` reads only the free program's steps, its pad exponent and the pad bound
of `SymFreeOk6`; v7 (`SymFreeOk7`) keeps those fields, so the budget takes them as hypotheses.

* **`sym_steps_gen`**.

Paper quantity of the main type: the SYM stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- **`sym_steps_le`, generic in the free program** (its steps `K_c(cap+1)²`, its pad exponent `K_r(n+1)^{D_r}`, the pad
`2^ρ` against the classes at `K_p`, `D_p`; any contract version): the SYM stage's steps within `c₄·seedClasses E₄`, `c₄` after `F`: the setup
at the capacity `2·2^{⌊n/8⌋+C_c}+2` (PA's data stage at `W = C_L(n+1)^D ≥ needW`, the numbers machine), the modulus
searches, the compiler writer's `c_W·2^{c_ψ^W ψ}n^{A^W_pre}`, the loop over any child family whose cells fit the pad
`2^ρ` of the free program `S` (v6), the sample expansion and a pad `P ≤ K_P·2^{⌊n/8⌋}`; `E₄` covers `E_W`'s
preprocessing and the pad's degree `D_p + 1`. -/
theorem sym_steps_gen (l : Literals) (F : GateFree l) (Kp Dp : ℕ)
    (Fp : FreeProg) (Kc : ℕ) (hKc : ∀ (cap : ℕ) (x : FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2)
    (Kr Dr : ℕ) (hKr : ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr)
    (hpad : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
      (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
        2 ^ Fp.val (C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 6 ≤
          Kp * (2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) * (n + 1) ^ Dp +
            2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2)))
    (h : SB)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hZ : h.Z = CallIndexR.capZR l) (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) (hfe : h.fe = F.filterErrDeg)
    (hcM : h.cM = CapNum.cMain (gateCap l) .sym)
    (D CL Cd Cc : ℕ) (hWL : ∀ n, PrimT.C4GateSym.needW n ≤ UnaryCalc.value D CL n)
    (EW E₄ : Envelope) (cW : ℕ) (hEc : EW.cpsi ≤ E₄.cpsi) (hEa : EW.Apre ≤ E₄.Apre) (hAt : Dp + 1 ≤ E₄.Atable)
    (KP : ℕ) :
    ∃ c₄ : ℕ, ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation) →
      ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
      100 * (2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) +
        h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1)) + 200000 ≤ 2 * 2 ^ C4Cap.capExp2 Cc n + 2 →
      ∀ (L : Lay), L.D = D → ∀ (Fm : C4Loop.ChildFam),
      Fm.cellCost + 1 ≤ 2 ^ Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6 →
      Fm.bound ≤ 8 * max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
        SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
        (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) →
      ∀ P : ℕ, P ≤ KP * 2 ^ (n / 8) →
      wrapCost (C4Cap.setupCost3 L (symReq n a ha Cs carriers translation).word n CL Cd Cc
          (2 * Data.coreCost a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n) + 2)
          (Data.unaryList (Data.symCounts a Cs carriers))
          (C4SymN.symBigCost (2 * 2 ^ C4Cap.capExp2 Cc n + 2) n F.cr F.filterErrDeg
            (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
            (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a carriers.length
            (UnaryCalc.value h.D2 h.C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum
            (Fp.cost (2 * 2 ^ C4Cap.capExp2 Cc n + 2) (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)))
          (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
            SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
            (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)))
          (0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
            C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs))
          (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)
          (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
            (((gate0 l F).budget kclk coef A a0 ha0).psiOf n)))
        Fm (2 ^ Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6)
        (C4Iface.sampCost (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) + 1 + P + 20 ≤
      c₄ * seedClasses E₄ n (((gate0 l F).budget kclk coef A a0 ha0).kOf n)
        (((gate0 l F).budget kclk coef A a0 ha0).psiOf n) := by
  -- the constants, all before the call
  obtain ⟨eq, heq⟩ : ∃ x, x = C4SymN.eQ l F.cr F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨cF, hcF⟩ := front_ex D CL Cd Cc h.Cw h.Dw
  obtain ⟨cd, hcd⟩ := ex_poly ((D + 1) * Data.symDc)
  obtain ⟨cu, hcu⟩ := ex_poly D
  obtain ⟨cl, hcl⟩ := ex_s (6 * eq)
  obtain ⟨c1, hc1⟩ := ex_poly 1
  obtain ⟨crr, hcrr⟩ := ex_poly Dr
  obtain ⟨cs, hcs⟩ := ex_s (9 * eq)
  obtain ⟨K0, hK0⟩ := C4Cap.mul_sq_le_div16 (2 * F.cr + 2)
  obtain ⟨Kq, hKq⟩ := C4Cap.mul_sq_le_div16 (2 * eq)
  obtain ⟨K1, hK1⟩ := C4Cap.mul_sq_le_div16 Dp
  refine ⟨2 ^ (Nat.clog 2 (2 ^ cF + Data.symCc * (2 * CL + Cd + 2) ^ Data.symDc * 2 ^ cd + 34 * (CL * 2 ^ cu) +
      22 * 2 ^ Cc + 2 * ((648000000 + 36 * Kc) * 2 ^ (3 * Cc)) + 600 * 2 ^ cl + 40 * 2 ^ c1 + 40 * (Kr * 2 ^ crr) +
      2097152 * 2 ^ cs + KP + 400) + K0) +
    (32 * (Kq + 1) + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + c1 + 1)) + cW, ?_⟩
  intro kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs hkq L hLD Fm hcell hb P hP
  have hn := PrimAsm.CallIndex.n_ge_two l F hs
  obtain ⟨hl2, hls, hq⟩ := ell_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
  rw [← heq] at hl2 hls hq
  obtain ⟨X, hX⟩ : ∃ x, x = 2 ^ (n / 8) := ⟨_, rfl⟩
  have ex1 : ∀ {c Y : ℕ}, Ex n 1 c Y → Y ≤ 2 ^ c * X := fun h' => by have := ex_of h'; rwa [one_mul, ← hX] at this
  -- the front
  have hw : (symReq n a ha Cs carriers translation).word.length ≤ h.Cw * (n + 1) ^ h.Dw :=
    le_trans (CallSize.gate_word_length_le l F kclk coef A a0 ha0 _ hcall) (hwb n)
  have hF := ex1 (hcF L hLD n _ hw)
  -- the data stage and the counts
  obtain ⟨hk2, hdesc, he⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨hL', hLX, h2, -, -, -, -, -, hcu', hK', hKX⟩ :=
    PrimT.C4GateSym.sym_data_hyps Cs carriers ha hk2 hdesc he (UnaryCalc.value D CL n) (hWL n)
  have hpoly := Data.coreCost_poly Cs carriers (UnaryCalc.value D CL n) (UnaryCalc.value D Cd n)
    (UnaryCalc.value D CL n) ha hk2 hL' hLX hK' hKX h2
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
  have hD : 2 * Data.coreCost a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n) + 2 ≤
      Data.symCc * (2 * CL + Cd + 2) ^ Data.symDc * 2 ^ cd * X := by
    rw [hLD]
    refine le_trans hpoly ?_
    have hp := hcd n
    have q1 := ex1 hp
    calc Data.symCc * (UnaryCalc.value D CL n + n + UnaryCalc.value D CL n + UnaryCalc.value D Cd n + 1) ^ Data.symDc
        ≤ Data.symCc * ((2 * CL + Cd + 2) * (n + 1) ^ (D + 1)) ^ Data.symDc :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
      _ = Data.symCc * (2 * CL + Cd + 2) ^ Data.symDc * (n + 1) ^ ((D + 1) * Data.symDc) := by
          rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ Data.symCc * (2 * CL + Cd + 2) ^ Data.symDc * (2 ^ cd * X) := Nat.mul_le_mul_left _ q1
      _ = _ := by ring
  have hU : (Data.unaryList (Data.symCounts a Cs carriers)).length ≤ CL * 2 ^ cu * X := by
    have e : (Data.unaryList (Data.symCounts a Cs carriers)).length =
        (Data.unaryList (carriers.map (·.length))).length +
          (Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length := by
      unfold Data.unaryList Data.symCounts; rw [List.flatMap_append, List.length_append]
    have q := ex1 (hcu n)
    have q2 : CL * (n + 1) ^ D ≤ CL * (2 ^ cu * X) := Nat.mul_le_mul_left _ q
    have e2 : UnaryCalc.value D CL n = CL * (n + 1) ^ D := rfl
    rw [e, mul_assoc]
    omega
  -- the numbers machine
  have hc0 := symN_le l F kclk coef A a0 ha0 h hwb hnw hZ hZm hCsp hJ hcX hK hcr hfe hcM ha Cs carriers translation
    hcall hs (2 * 2 ^ C4Cap.capExp2 Cc n + 2)
    (Fp.cost (2 * 2 ^ C4Cap.capExp2 Cc n + 2) (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)) hkq
  have hc := symBig_cap_le Cc n Kc _ _ hc0 (hKc _ _)
  -- the modulus searches
  obtain ⟨ell, hell⟩ : ∃ x, x = max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
      SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
      (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers)) := ⟨_, rfl⟩
  rw [← hell] at hl2 hb ⊢
  have hl : 2 ^ (3 * ell) ≤ 2 ^ cl * X := by
    have q := ex1 (hcl n)
    refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) q
    have e : 6 * eq * (natBitLength n + 1) ^ 2 = 3 * (2 * eq * C4Cap.bsq n) := by unfold C4Cap.bsq; ring
    rw [e]; omega
  -- the center bits
  have hd2 := d2_le ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  have hkn : ((gate0 l F).budget kclk coef A a0 ha0).kOf n ≤ n := ((callInputs l F kclk coef A a0 ha0).starParams n hs).k_le_n
  have hd2' : 0 + C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) +
      C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ 2 ^ c1 * X := by
    have q := ex1 (hc1 n)
    rw [pow_one] at q
    have e : ((callInputs l F kclk coef A a0 ha0).starParams n hs).n = n := rfl
    omega
  -- the pad's exponent
  have hρ : Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6 ≤ Kr * 2 ^ crr * X := by
    have q := ex1 (hcrr n)
    have r := hKr (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)
    have e : (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs).n = n := rfl
    rw [e] at r
    rw [mul_assoc]
    exact le_trans r (Nat.mul_le_mul_left _ q)
  -- the sample expansion
  have hs' : C4Iface.sampCost (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ≤ 2097152 * 2 ^ cs * X := by
    have q := ex1 (hcs n)
    have s1 := samp_le (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
    have eQd : (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).Q =
        SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers := rfl
    rw [eQd] at s1
    obtain ⟨e, he⟩ : ∃ x, x = eq * C4Cap.bsq n := ⟨_, rfl⟩
    have e2 : 2 * eq * C4Cap.bsq n = 2 * e := by rw [he]; ring
    rw [e2] at hls
    rw [← he] at hq
    have b1 : SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers + 1 ≤ 2 * 2 ^ e := by
      have := Nat.one_le_two_pow (n := e); omega
    have b2 : 2 ^ (4 * (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell) ≤ 2 ^ (8 * e) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : 9 * eq * (natBitLength n + 1) ^ 2 = 9 * e := by rw [he]; unfold C4Cap.bsq; ring
    rw [e3] at q
    calc C4Iface.sampCost (C4Val.symSP (callInputs l F kclk coef A a0 ha0) hs Cs carriers)
        ≤ 1048576 * (2 * 2 ^ e) * 2 ^ (8 * e) := le_trans s1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ b1) b2)
      _ = 2097152 * 2 ^ (9 * e) := by rw [mul_assoc, mul_assoc, ← pow_add, ← mul_assoc]; ring_nf
      _ ≤ 2097152 * (2 ^ cs * X) := Nat.mul_le_mul_left _ q
      _ = _ := by ring
  -- the rest at rate 3, then the budget
  rw [← hX] at hP
  have hR := rest_le L (symReq n a ha Cs carriers translation).word n CL Cd Cc _ _ _ ell _ _ _ P
    (2 ^ cF) (Data.symCc * (2 * CL + Cd + 2) ^ Data.symDc * 2 ^ cd) (CL * 2 ^ cu)
    ((648000000 + 36 * Kc) * 2 ^ (3 * Cc)) (2 ^ cl) (2 ^ c1) (Kr * 2 ^ crr) (2097152 * 2 ^ cs) KP
    (hX ▸ hF) (hX ▸ hD) (hX ▸ hU) hc (hX ▸ hl) (hX ▸ hd2') (hX ▸ hρ) (hX ▸ hs') (hX ▸ hP)
  have hk : ((gate0 l F).budget kclk coef A a0 ha0).kOf n ≤ n / 16 + K0 :=
    le_trans (C4SymN.kOf_le_bsq l F kclk coef A a0 ha0 n) (hK0 n)
  have hlin : ell ≤ (Kq + 1) * (n + 1) := by
    have q := hKq n
    have e : 2 * eq * C4Cap.bsq n = 2 * eq * (natBitLength n + 1) ^ 2 := rfl
    have e2 : (Kq + 1) * (n + 1) = Kq * n + Kq + n + 1 := by ring
    omega
  have hK2 : n + 1 ≤ 2 ^ (n / 8 + c1) := by
    have q := hc1 n
    unfold Ex at q
    rw [pow_one, one_mul] at q
    exact q
  exact budget_le E₄ EW n _ _ _ _ ell _ _ _ _ K0 (Kq + 1) Kp Dp K1 c1 cW (by omega)
    (wrap_split L _ n CL Cd Cc _ _ _ ell _ _ _ Fm _ P hcell hb) hR hk hkn hlin hd2
    (hpad kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs) (hK1 n) hK2 le_rfl hEc hEa hAt

end NearCubicWires.WireExponent3_5.PrimT.C4Bud

end
