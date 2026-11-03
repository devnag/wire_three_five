import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC
import Proof.Wire_3_5.Primitive.SeedFix.C4CapF
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNEBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SYM item (b) v2: the SYM numbers machine at the unary capacity `2·2^{⌊n/8⌋ + C} + 2`

P3:2929-2941, 2994-3000, 3011-3016, 3098-3100 (the selection class `2^{q/2 + c_sel k}`), P3:3105-3115: `sym_bigS`
(M61) at the capacity v2: the M61 sizes `2^{O((B+1)²)}` fit `2^{⌊n/8⌋ + C}` through `C4Cap.mul_sq_le_div16`, and the
free numbers (contract v5: `K·2^{⌊n/8⌋}`) fit once `C ≥ ⌈log₂ K⌉ + 1`.

* `fitA`, `of_K`, `add8`, `mono8`, **`sym_fits2`**, **`sym_bigS2`**.

Paper quantities of the main type: the SYM stage's words at the call's `Q`, `ℓ`, `n_T`, `dRow`, and the capacity
`2^{⌊n/8⌋ + C}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymN
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- **The SYM call's sizes fit the capacity v2** `2^{⌊n/8⌋ + C}` once `C ≥ C₀`. -/
theorem sym_fits2 (l : Literals) (F : GateFree l) (Fp : FreeProg)
    (hok : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), C4SymW.FreeSmall Ds x → Ko * 2 ^ (x.n / 8) ≤ cap → Fp.ok cap x)
    (hval : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), C4SymW.FreeSmall Ds x → j.val ≠ 6 →
      Fp.val x j ≤ Kv * 2 ^ (x.n / 8))
    (hrho : ∃ Kr Dr : ℕ, ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr)
    (h : SB) (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hZ : h.Z = CallIndexR.capZR l) (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) (hfe : h.fe = F.filterErrDeg)
    (hcM : h.cM = CapNum.cMain (gateCap l) .sym) :
    ∃ Cc0 : ℕ, ∀ Cc : ℕ, Cc0 ≤ Cc → ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation) → ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
      Fp.ok (2 * (2 ^ C4Cap.capExp2 Cc n) + 2) (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) ∧ (∀ j, Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) j + 1 ≤ (2 ^ C4Cap.capExp2 Cc n)) ∧ (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧ (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧
      (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) * (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) * (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧ 2 ^ (wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧
      (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) * (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) * (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)) * 2 ^ wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧ 4 * (n + 2) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧
      (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0 + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧
      (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) * 8 * ((max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + 1) + Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1 + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧
      wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 + Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0 + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧ (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) * 8 + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧ 3 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 ≤ (2 ^ C4Cap.capExp2 Cc n) ∧
      (100 * (2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) + h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1)) + 200000) ≤ 2 * (2 ^ C4Cap.capExp2 Cc n) + 2 := by
  -- the constants
  obtain ⟨Kr, Dr, hr⟩ := hrho
  obtain ⟨eA, heA⟩ : ∃ x, x = e0 F.cr h := ⟨_, rfl⟩
  obtain ⟨eq, heq⟩ : ∃ x, x = eQ l F.cr F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨ek, hek⟩ : ∃ x, x = 2 * F.cr + 2 := ⟨_, rfl⟩
  obtain ⟨eW, heW⟩ : ∃ x, x = 9 + 8 * (ek + eq) + 8 * ek := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ x, x = eA + eq + eW + ek + 40 := ⟨_, rfl⟩
  obtain ⟨Ko, hok'⟩ := hok Ds
  obtain ⟨Kv, hval'⟩ := hval Ds
  obtain ⟨eR, heR⟩ : ∃ x, x = Nat.clog 2 Kr + Dr := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ x, x = 4 * (eA + eq + eW + ek + eR + Ds) + 40 := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := C4Cap.mul_sq_le_div16 U
  -- the exponents' order
  have xA : eA ≤ U := by omega
  have xq : eq ≤ U := by omega
  have xk : ek ≤ U := by omega
  have xW : eW + 0 ≤ U := by omega
  have xAW : eA + eW ≤ U := by omega
  have x5 : 4 + 1 ≤ U := by omega
  have xR : eR ≤ U := by omega
  have xd0 : ek ≤ U := by omega
  have xd1 : ek + eq + 8 + (2 * (ek + eq) + 1) ≤ U := by omega
  have xd3 : eW ≤ U := by omega
  have xd4 : ek + eq + 8 ≤ U := by omega
  have xl : 3 * (ek + eq) + eq + 1 ≤ U := by omega
  have y1 : 1 ≤ Ds := by omega
  have yk : ek ≤ Ds := by omega
  have y4 : 4 ≤ Ds := by omega
  have y2 : 2 ≤ Ds := by omega
  have yA : eA ≤ Ds := by omega
  have y30 : 4 + 26 ≤ Ds := by omega
  have yq : eq ≤ Ds := by omega
  have ykq : ek + eq ≤ Ds := by omega
  have yW : eW ≤ Ds := by omega
  have y5 : 4 + 1 ≤ Ds := by omega
  refine ⟨2 * K0 + Nat.clog 2 Ko + Nat.clog 2 Kv + 12,
    fun Cc hCc kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs => ?_⟩
  -- the size unit `s = (B+1)²`, `e = ⌊n/8⌋` and `M = 2^{e + Cc}`
  obtain ⟨s, hsd⟩ : ∃ x, x = C4Cap.bsq n := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := hsd ▸ C4Cap.bsq_pos n
  obtain ⟨e, hed⟩ : ∃ x, x = n / 8 := ⟨_, rfl⟩
  obtain ⟨M, hMd⟩ : ∃ x, x = 2 ^ C4Cap.capExp2 Cc n := ⟨_, rfl⟩
  have hMe : M = 2 ^ (e + Cc) := by rw [hMd, hed]; rfl
  rw [← hMd]
  have hUs : U * s ≤ e + K0 := by
    have h1 := hK0 n
    have h2 : U * s = U * (natBitLength n + 1) ^ 2 := by rw [hsd]; rfl
    omega
  have toE : ∀ {X a : ℕ}, X ≤ 2 ^ (a * s) → a ≤ U → X ≤ 2 ^ (e + K0) := fun hX ha =>
    le_trans hX (Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.mul_le_mul_right s ha) hUs))
  have fit8 : ∀ {X c : ℕ}, X ≤ 2 ^ (e + c) → c + 1 ≤ Cc → X + 1 ≤ M := fun hX hc => by
    rw [hMe]; exact fitA hX (by omega)
  have fit : ∀ {X a : ℕ}, X ≤ 2 ^ (a * s) → a ≤ U → X + 1 ≤ M := fun hX ha => fit8 (toE hX ha) (by omega)
  have pwl : ∀ {x e : ℕ}, x ≤ e * s → x ≤ 2 ^ (e * s) := fun hx => C4Cap.pw_lin hx
  have pwc : ∀ {X c : ℕ}, X ≤ c → X ≤ 2 ^ (c * s) := fun hX => C4Cap.pw_const hs1 hX
  have pwp : ∀ {X Y a b : ℕ}, X ≤ 2 ^ (a * s) → Y ≤ 2 ^ (b * s) → X * Y ≤ 2 ^ ((a + b) * s) :=
    fun hX hY => C4Cap.pw_mul hX hY
  have hsz : ∀ {X e' : ℕ}, X ≤ 2 ^ (e' * s) → e' ≤ Ds → X ≤ 2 ^ (Ds * C4Cap.bsq n) := fun hX he => by
    rw [← hsd]; exact C4Cap.pw_mono he hX
  -- the call's facts
  obtain ⟨hk2, hdesc, -⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have h2kh := HashFam.fam_two_kh l F kclk coef A a0 ha0 hs
  have hk := kOf_le_bsq l F kclk coef A a0 ha0 n
  rw [← hek, ← hsd] at hk
  have hkq := kq_le l F kclk coef A a0 ha0 h n
  rw [← heA, ← hsd] at hkq
  have hQ0 := q_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
  rw [← heq, ← hsd] at hQ0
  have hn2 : n + 2 ≤ 2 ^ (1 * s) := by rw [hsd]; exact C4Cap.n2_pw n
  obtain ⟨-, -, -, -, -, -, -, hv0, hG0⟩ := sym_needs l F kclk coef A a0 ha0 h hwb hnw hZ hZm hCsp hJ hcX hK hcr hfe
    hcM ha Cs carriers translation hcall hs _ le_rfl
  have hKQ0 : (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) * (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) * (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)) ≤ 2 ^ (eA * s) :=
    le_trans hG0 (le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) (Nat.le_add_right _ _)) hkq)
  have hCS : (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) ≤ (100 * (2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) + h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1)) + 200000) := hv0 0
  have hkk : (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) ≤ ek * s := by
    have e' : (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) = 2 * (((callInputs l F kclk coef A a0 ha0).starParams n hs).s * (((callInputs l F kclk coef A a0 ha0).starParams n hs).r / 2)) := by unfold SeedFix.callKh; ring
    rw [e', h2kh]; exact hk
  have hcq : Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ≤ eq * s := C4Cap.clog_pw hQ0
  have hell : (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) ≤ (ek + eq) * s :=
    max_le (le_trans hkk (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      (le_trans hcq (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))
  have hw1 : wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 ≤ eW * s := by
    rw [heW]; exact w_le hell hkk hs1
  have hl3 : (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + 1 ≤ (2 * (ek + eq) + 1) * s := l3_le hell hs1
  have h3l : 3 * (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) ≤ 3 * (ek + eq) * s := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 3 hell
  have hcy : ∀ c ∈ SymDec.cyOf Cs, c ≤ (n + 1) ^ 26 := by
    intro c hc
    unfold SymDec.cyOf at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact Data.symGates_len_le (Cs i) _ (hdesc i)
  have hys : (SymDec.cyOf Cs).sum ≤ 4 * (n + 1) ^ 26 := by
    have h1 := List.sum_le_card_nsmul (SymDec.cyOf Cs) ((n + 1) ^ 26) hcy
    rw [SymDec.cyOf_length, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ ha)
  have h26 : (n + 1) ^ 26 ≤ 2 ^ (26 * s) :=
    le_trans (Nat.pow_le_pow_left (Nat.le_succ _) 26) (by rw [hsd]; exact C4Cap.pow_pw 26 n)
  have hSm : 4 * (n + 2) ≤ 2 ^ ((4 + 1) * s) := pwp (pwc (le_refl 4)) hn2
  -- the call's numbers are small
  have hFS : C4SymW.FreeSmall Ds (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) :=
    symX_small (callInputs l F kclk coef A a0 ha0) Cs carriers hs Ds (hsz (le_trans (Nat.le_add_right n 2) hn2) y1)
      (hsz (pwl (le_trans (Nat.le_add_left _ _) hkk)) yk)
      (hsz (pwl (by rw [one_mul, hsd]; exact C4Cap.lq_le_bsq n)) y1) (hsz (le_trans hCS hkq) yA)
      (hsz (pwc ha) y4) (hsz (pwc hk2) y2) (hsz (le_trans hys (pwp (pwc (le_refl 4)) h26)) y30) (hsz hQ0 yq)
      (hsz (pwl hell) ykq)
      (hsz (le_of_eq_of_le (C4SymL.symNT_link (callInputs l F kclk coef A a0 ha0) Cs carriers hs ha rfl rfl).symm hKQ0) yA)
      (hsz (pwl (le_trans (Nat.le_succ _) hw1)) yW) (hsz (le_trans (dRow_le ((callInputs l F kclk coef A a0 ha0).starParams n hs)) hSm) y5)
  -- the free numbers
  have hfv : ∀ j : Fin 7, Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) j ≤ 2 ^ (e + (Nat.clog 2 Kv + K0)) := by
    intro j
    by_cases hj : j.val = 6
    · have hj' : j = 6 := Fin.ext hj
      subst hj'
      have h2 : (n + 1) ^ Dr ≤ 2 ^ (Dr * s) :=
        le_trans (Nat.pow_le_pow_left (Nat.le_succ _) Dr) (by rw [hsd]; exact C4Cap.pow_pw Dr n)
      have h3 : Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 6 ≤ Kr * 2 ^ (Dr * s) := le_trans (hr _) (Nat.mul_le_mul_left _ h2)
      exact mono8 (by omega) (toE (C4Cap.pw_K hs1 h3) (by rw [heR] at xR; exact xR))
    · have h3 : Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) j ≤ Kv * 2 ^ e := by rw [hed]; exact hval' _ j hFS hj
      exact mono8 (by omega) (of_K h3)
  have fv : ∀ j : Fin 7, Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) j + 1 ≤ M := fun j => fit8 (hfv j) (by omega)
  have hF : Fp.ok (2 * M + 2) (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) := by
    apply hok' _ _ hFS
    have h1 : Ko * 2 ^ e ≤ 2 ^ (e + Nat.clog 2 Ko) := of_K le_rfl
    have h2 := fit8 h1 (by omega)
    have h3 : Ko * 2 ^ e ≤ 2 * M + 2 := by omega
    rw [hed] at h3
    exact h3
  have hkkE : (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) ≤ 2 ^ (e + K0) := toE (pwl hkk) xk
  have hd1E : (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) * 8 * ((max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))) + 1) ≤ 2 ^ (e + K0) :=
    toE (pwp (pwp (pwl hell) (pwc (le_refl 8))) (pwl hl3)) xd1
  have hw1E : wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 ≤ 2 ^ (e + K0) := toE (pwl hw1) xd3
  exact ⟨hF, fv, fit hQ0 xq, fit (pwl hkk) xk, fit hKQ0 xA,
    fit (C4Cap.pw_exp (le_of_le_of_eq hw1 (by rw [Nat.add_zero]))) xW,
    fit (pwp hKQ0 (C4Cap.pw_exp (le_trans (Nat.le_succ _) hw1))) xAW, fit hSm x5,
    fit8 (add8 hkkE (hfv 0)) (by omega), fit8 (add8 hd1E (hfv 1)) (by omega),
    fit8 (add8 hw1E (hfv 0)) (by omega), fit (pwp (pwl hell) (pwc (le_refl 8))) xd4,
    fit (C4Cap.pw_add hs1 (pwl h3l) hQ0) xl, le2 (fit hkq xA)⟩

/-- **The SYM numbers machine at the unary capacity v2** `2·2^{⌊n/8⌋ + C} + 2`, at every SYM call of the gate, for every
free program whose program runs above `K·2^{⌊n/8⌋}` and whose values stay below it. -/
theorem sym_bigS2 (l : Literals) (F : GateFree l) (Fp : FreeProg)
    (hok : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), C4SymW.FreeSmall Ds x → Ko * 2 ^ (x.n / 8) ≤ cap → Fp.ok cap x)
    (hval : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), C4SymW.FreeSmall Ds x → j.val ≠ 6 →
      Fp.val x j ≤ Kv * 2 ^ (x.n / 8))
    (hrho : ∃ Kr Dr : ℕ, ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr)
    (h : SB) (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hZ : h.Z = CallIndexR.capZR l) (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr) (hfe : h.fe = F.filterErrDeg)
    (hcM : h.cM = CapNum.cMain (gateCap l) .sym) :
    ∃ Cc0 : ℕ, ∀ Cc : ℕ, Cc0 ≤ Cc → ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation) → ∀ hs : (callInputs l F kclk coef A a0 ha0).StarAt n,
      SymBig Fp F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) (2 * (2 ^ C4Cap.capExp2 Cc n) + 2)
        (symBigCost (2 * (2 ^ C4Cap.capExp2 Cc n) + 2) n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
          (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a carriers.length
          (UnaryCalc.value h.D2 h.C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum (Fp.cost (2 * (2 ^ C4Cap.capExp2 Cc n) + 2) (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs)))
        (callInputs l F kclk coef A a0 ha0) ha Cs carriers translation hs := by
  obtain ⟨Cc0, hC0⟩ := sym_fits2 l F Fp hok hval hrho h hwb hnw hZ hZm hCsp hJ hcX hK hcr hfe hcM
  refine ⟨Cc0, fun Cc hCc kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs => ?_⟩
  obtain ⟨hF, fv, fQ, fkk, fG, fW, fcnt, fSm, fd0, fd1, fd3, fd4, fl, hcap'⟩ :=
    hC0 Cc hCc kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs
  obtain ⟨M, hMd⟩ : ∃ x, x = 2 ^ C4Cap.capExp2 Cc n := ⟨_, rfl⟩
  rw [← hMd] at hF fv fQ fkk fG fW fcnt fSm fd0 fd1 fd3 fd4 fl hcap'
  rw [← hMd]
  obtain ⟨hN1, hKb, hC, hcS, hcP, hcC, hN2, hv, -⟩ := sym_needs l F kclk coef A a0 ha0 h hwb hnw hZ hZm hCsp hJ hcX
    hK hcr hfe hcM ha Cs carriers translation hcall hs (2 * M + 2) hcap'
  obtain ⟨hk2, -, -⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a0 ha0 hs
  have hcl : (Data.symCodes a Cs).length = a := by unfold Data.symCodes; simp
  obtain ⟨sb1, sb2, sb3, -, sb5, sb6, -, sb8⟩ := star_small ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  obtain ⟨hsc, hdc, cdd, cQl, cQ, cl, ck, ccnt, cd2, c17⟩ := caps_of M (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)) ((callInputs l F kclk coef A a0 ha0).starParams n hs).b ((callInputs l F kclk coef A a0 ha0).starParams n hs).s
    ((callInputs l F kclk coef A a0 ha0).starParams n hs).r ((callInputs l F kclk coef A a0 ha0).starParams n hs).n (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 0) (Fp.val (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) 1) fQ fkk fG fW fcnt fSm sb1 sb2 sb3 sb5 sb6 sb8
    Nat.one_le_two_pow Nat.one_le_two_pow (stV_pos _ _ _ _) (fv 0) (fv 1) fd0 fd1 fd3 fd4 fl
  have hNT : (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) * (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) * (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)) = Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers := C4SymL.symNT_link (callInputs l F kclk coef A a0 ha0) Cs carriers hs ha rfl rfl
  have hQl : (symInOf (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) n (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) carriers.length a (SymDec.cyOf Cs)).Q =
      (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) := C4SymL.symQ_link (callInputs l F kclk coef A a0 ha0) Cs carriers hs ha rfl rfl
  -- `bigS_spec`'s premises
  have a_hw : (symReq n a ha Cs carriers translation).word = Data.reqW ((callInputs l F kclk coef A a0 ha0).starParams n hs).n false (Data.symCodes a Cs)
      (carriers.map Carrier.code) (RepairRepresentation.natListWord translation) :=
    (ReqBridge.reqW_symReq ha Cs carriers translation).symm
  have a_ccs : (carriers.map Carrier.code).length = (carriers.map (·.length)).length := by
    rw [List.length_map, List.length_map]
  have a_cx : (carriers.map (·.length)).length ≤ 2 := by rw [List.length_map]; exact hk2
  have a_cy : (SymDec.cyOf Cs).length ≤ 4 := by rw [SymDec.cyOf_length]; exact ha
  have a_N2 : SymDec.NumsNeed (2 * M + 2) ((callInputs l F kclk coef A a0 ha0).starParams n hs).n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n) (SymDec.cyOf Cs).sum
      (carriers.map (·.length)).length (Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Data.symCodes a Cs).length
      ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0) := by
    rw [List.length_map, hcl]; exact hN2
  have a_Q : 2 * (symInOf (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) ((callInputs l F kclk coef A a0 ha0).starParams n hs).n (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n) (Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
      (carriers.map (·.length)).length (Data.symCodes a Cs).length (SymDec.cyOf Cs)).Q ≤ 2 * M + 2 := by
    rw [List.length_map, hcl]
    show 2 * (symInOf (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) n (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) carriers.length a (SymDec.cyOf Cs)).Q ≤
      2 * M + 2
    rw [hQl]
    exact le_trans (Nat.mul_le_mul_left 2 (Nat.le_of_succ_le fQ)) (Nat.le_add_right _ _)
  have a_v : ∀ j : Fin 11, (![(((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n), ((callInputs l F kclk coef A a0 ha0).starParams n hs).n, F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n, Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n, (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)),
      (carriers.map (·.length)).length, (Data.symCodes a Cs).length, (SymDec.cyOf Cs).getD 0 0,
      (SymDec.cyOf Cs).getD 1 0, (SymDec.cyOf Cs).getD 2 0, (SymDec.cyOf Cs).getD 3 0] : Fin 11 → ℕ) j ≤ 2 * M + 2 := by
    rw [List.length_map]; exact hv
  have a_Qd : (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) = (symInOf (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) ((callInputs l F kclk coef A a0 ha0).starParams n hs).n (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n) (Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))
      (carriers.map (·.length)).length (Data.symCodes a Cs).length (SymDec.cyOf Cs)).Q := by
    rw [List.length_map, hcl]; exact hQl.symm
  have a_fs : (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) = 2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV (carriers.map (·.length)).length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n))
      (Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n + 5) := by
    show (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) = 2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV (carriers.map (·.length)).length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)
    rw [List.length_map]
  have a_x : (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) = ⟨((callInputs l F kclk coef A a0 ha0).starParams n hs).n, (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)), Ledger.Lq ((callInputs l F kclk coef A a0 ha0).starParams n hs).n, (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n), (Data.symCodes a Cs).length, (carriers.map (·.length)).length,
      (SymDec.cyOf Cs).sum, (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers), (max ((SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) + (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs))) (Nat.clog 2 (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers))), (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) * (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) * (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)), wOf (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers), ((((callInputs l F kclk coef A a0 ha0).starParams n hs).n - ((callInputs l F kclk coef A a0 ha0).starParams n hs).r * ((callInputs l F kclk coef A a0 ha0).starParams n hs).b + 1) / 2 + (((callInputs l F kclk coef A a0 ha0).starParams n hs).b - ((callInputs l F kclk coef A a0 ha0).starParams n hs).s) * (((callInputs l F kclk coef A a0 ha0).starParams n hs).r / 2))⟩ := by
    rw [C4SymL.symX_eq (callInputs l F kclk coef A a0 ha0) Cs carriers hs ha rfl rfl, C4SymL.symQ_link (callInputs l F kclk coef A a0 ha0) Cs carriers hs ha rfl rfl,
      C4SymL.symNT_link (callInputs l F kclk coef A a0 ha0) Cs carriers hs ha rfl rfl, List.length_map, hNT]
    rfl
  obtain ⟨τ, c, e, hcost, hsym, hrest, -⟩ := bigS_spec Fp (2 * M + 2) F.cr F.filterErrDeg (gateZeta_pos l)
    (gateZeta_lt l) (gateCδ1 l) (gateCap l) ((callInputs l F kclk coef A a0 ha0).starParams n hs) rfl (symReq n a ha Cs carriers translation).word
    (Data.symCodes a Cs) (carriers.map Carrier.code) (RepairRepresentation.natListWord translation)
    (carriers.map (·.length)) (SymDec.cyOf Cs) (UnaryCalc.value h.D2 h.C2 n) ((n + 1) ^ 26) (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)
    (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) a_hw a_ccs a_cx a_cy hKb hC hN1 rfl rfl rfl rfl hcS hcP hcC
    a_N2 (le_trans (by norm_num) hn8) a_Q a_v (SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers) (2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits) (2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5)) (SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0)) a_Qd rfl a_fs rfl hsc (C4SymW.symX (callInputs l F kclk coef A a0 ha0) Cs carriers hs) a_x hF hdc cQl cQ cl ck
    (fun j => le2' (fv j)) cdd ccnt cd2 c17
  unfold SymBig
  refine ⟨τ, c, e, ?_, ?_, fun j => ?_⟩
  · rw [List.length_map, hcl] at hcost; exact hcost
  · rw [hrest _ sk0_ne_symO]; exact blankD_st0 _ _
  · have h1 := hsym j
    rw [hNT, C4SymL.dRow_link] at h1
    exact h1

end NearCubicWires.WireExponent3_5.PrimT.C4SymN

end
