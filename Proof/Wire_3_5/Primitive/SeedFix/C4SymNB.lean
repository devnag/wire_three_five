import Lean
import Proof.Wire_3_5.Primitive.Writers.SymFamBase
import Proof.Wire_3_5.Primitive.SeedFix.C4CapD
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.Primitive.SeedFix.C4CapE
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNBBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SYM item (b), part 2: the SYM call's sizes below `2^{a(B+1)²}`

P3:3105-3115 (every size at an on-star call is `2^{O(k)}·poly(n)`), P3:1189 (`k = r·⌊log₂(n/r+1)⌋`, `r = rowBr c_r n`),
P3:2987-2988 (`Q = samp:q`): at a SYM call of the gate, the numbers front's load `100·K_Q + 200000`, the sample count
`Q` and the star width `k` are below `2^{e·(B+1)²}` for constants `e` of the gate and the base constants alone, and
the star's small numbers are below `2n`.

* `eKQ`, `e0`, `eQ`; `kOf_le_bsq`, **`kq_le`**, **`q_le`**, `star_small`.

Paper quantities of the main type: `K_Q`, `Q`, `k` at a SYM call against `2^{(B+1)²}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymN
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive

/-- The exponent of the SYM sample count. -/
noncomputable def eQ (l : Literals) (cr fe : ℕ) : ℕ :=
  Nat.clog 2 (16384 * CallIndexR.symKI cr) + (2 * cr + 2 + (CallIndexR.symZI l fe + 2))

/-- The star width is `O((B+1)²)`. -/
theorem kOf_le_bsq (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n : ℕ) :
    ((gate0 l F).budget kclk coef A a0 ha0).kOf n ≤ (2 * F.cr + 2) * C4Cap.bsq n :=
  C4Cap.starWidth_le_bsq F.cr n

/-- **The numbers front's load is below `2^{e₀(B+1)²}`.** -/
theorem kq_le (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (h : SB) (n : ℕ) :
    100 * (2 ^ h.cA * (2 ^ (((gate0 l F).budget kclk coef A a0 ha0).kOf n + Nat.clog 2 (n + 2) +
      h.KF * Nat.clog 2 (n + 2) ^ 2 + 0) + 1)) + 200000 ≤ 2 ^ (e0 F.cr h * C4Cap.bsq n) := by
  have hk := kOf_le_bsq l F kclk coef A a0 ha0 n
  have hL : Nat.clog 2 (n + 2) ≤ natBitLength n + 1 := C4Cap.lq_le n
  have hLb : Nat.clog 2 (n + 2) ≤ C4Cap.bsq n := le_trans hL (C4Cap.b1_le_bsq n)
  have hL2 : Nat.clog 2 (n + 2) ^ 2 ≤ C4Cap.bsq n := Nat.pow_le_pow_left hL 2
  have hs1 := C4Cap.bsq_pos n
  obtain ⟨s, hsd⟩ : ∃ s, s = C4Cap.bsq n := ⟨_, rfl⟩
  obtain ⟨k, hkd⟩ : ∃ k, k = ((gate0 l F).budget kclk coef A a0 ha0).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hsd, ← hkd] at hk
  rw [← hsd, ← hLd] at hLb hL2
  rw [← hsd] at hs1
  rw [← hsd, ← hkd, ← hLd]
  have hKFL : h.KF * L ^ 2 ≤ h.KF * s := Nat.mul_le_mul_left _ hL2
  have e1 : (2 * F.cr + 4 + h.KF) * s = (2 * F.cr + 2) * s + s + s + h.KF * s := by ring
  obtain ⟨m, hmd⟩ : ∃ m, m = k + L + h.KF * L ^ 2 + 0 := ⟨_, rfl⟩
  rw [← hmd]
  have hm : m + 1 ≤ (2 * F.cr + 4 + h.KF) * s := by omega
  have h2 : 2 ^ m + 1 ≤ 2 ^ ((2 * F.cr + 4 + h.KF) * s) := by
    have h0 := Nat.one_le_two_pow (n := m)
    have h3 : 2 ^ (m + 1) ≤ 2 ^ ((2 * F.cr + 4 + h.KF) * s) := C4Cap.pw_exp hm
    rw [pow_succ] at h3
    omega
  have h4 : 2 ^ h.cA ≤ 2 ^ (h.cA * s) := C4Cap.pw_exp (Nat.le_mul_of_pos_right _ hs1)
  have hKQ := C4Cap.pw_mul h4 h2
  have h100 : 100 ≤ 2 ^ (7 * s) := le_trans (by norm_num) (C4Cap.pw_exp (Nat.le_mul_of_pos_right 7 hs1))
  have h2e5 : 200000 ≤ 2 ^ (18 * s) := le_trans (by norm_num) (C4Cap.pw_exp (Nat.le_mul_of_pos_right 18 hs1))
  exact C4Cap.pw_add hs1 (C4Cap.pw_mul h100 hKQ) h2e5

/-- **The SYM sample count is below `2^{e_Q(B+1)²}`.** -/
theorem q_le (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) :
    SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers ≤
      2 ^ (eQ l F.cr F.filterErrDeg * C4Cap.bsq n) := by
  obtain ⟨hk2, hdesc, -⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hQ := CallIndexR.symCount_leK l F kclk coef A a0 ha0 n hs ha Cs carriers hdesc hk2
  have hs1 := C4Cap.bsq_pos n
  have hk := kOf_le_bsq l F kclk coef A a0 ha0 n
  have h1 : 2 ^ (5 * ((gate0 l F).budget kclk coef A a0 ha0).kOf n / 8) ≤ 2 ^ ((2 * F.cr + 2) * C4Cap.bsq n) :=
    C4Cap.pw_exp (by omega)
  have h2 := C4Cap.pow_pw (CallIndexR.symZI l F.filterErrDeg + 2) n
  have h3 := C4Cap.pw_mul h1 h2
  have h4 : SeedFix.symCount (callInputs l F kclk coef A a0 ha0) hs Cs carriers ≤
      (16384 * CallIndexR.symKI F.cr) *
        2 ^ ((2 * F.cr + 2 + (CallIndexR.symZI l F.filterErrDeg + 2)) * C4Cap.bsq n) :=
    le_trans hQ (le_of_eq_of_le (Nat.mul_assoc _ _ _) (Nat.mul_le_mul_left _ h3))
  exact C4Cap.pw_K hs1 h4

end NearCubicWires.WireExponent3_5.PrimT.C4SymN

end
