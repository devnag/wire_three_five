import Lean
import Proof.Wire_3_5.FinalPass.SymCap2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SymDegBase


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM request's degree bound is linear: `D ≤ d_D(⌊√B_S⌋ + L)`

list:base P3:1376-1398 (`J = ⌈log₂B⌉ + 9` windows `W_j = 64 + ⌈⌈√(64²B)⌉/2^{⌊j/3⌋}⌉`, so `Σ_j W_j = O(√B + J)`),
P3:3094-3100 (`d_S = C_D(√B_S + L)`): the degree bound `D = max(384·w_f + 1, 3·lbP)` of the SYM rows' factors
(the `sym_factor_count`) is at most `symDD·(⌊√B_S⌋ + L)`, `symDD = 780(48 + Z) + 384f_e + 436876` fixed before `F`
(`B_S ≤ capK(c_r)(n+2)^Z ≤ 2^{(48+Z)L}` since `2c_r + 2 ≤ n + 2`). The geometric sum replaces the product bound
`lbP_le` (`J·√B`), which is not linear. This is `hpre_sym`'s `D ≤ d` at the SYM batch.

* `sum_div_pow_le`, `sum_div_pow3_le`, `ceilDiv_le`, **`lbP_lin`**, `symDD`, **`symDg_lin`**.

Paper quantity of the main type: the SYM degree `d_S` (P3:3094-3100). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.Lists
open Finset

/-- **The SYM degree constant** (`symDD ≤ d_D`, fixed before `F`). -/
noncomputable def symDD (l : Literals) (fe : ℕ) : ℕ := 780 * (48 + CallIndexR.capZR l) + 384 * fe + 436876

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The SYM degree bound is `≤ symDD·(⌊√B_S⌋ + L)`.** -/
theorem symDg_lin (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    symDg l F kclk coef A a ha Cs carriers ≤ symDD l F.filterErrDeg *
      (Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) + Nat.clog 2 (n + 2)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hL1 := one_le_L n
  have hn2 := n2_le_L n
  have h1 : ((callInputs l F kclk coef A a ha).filterParams .sym n).walkLen ≤
      F.filterErrDeg * Nat.clog 2 (n + 2) + 1 :=
    UnionMachine.FiltPipeLe.walkLen_le ((callInputs l F kclk coef A a ha).filterParams .sym n)
  obtain ⟨C, hCd⟩ : ∃ C, C = ((gate0 l F).budget kclk coef A a ha).capOf .sym n := ⟨_, rfl⟩
  have hB : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.B ≤ 8192 * C := by
    show carriers.length * (4096 * ((gate0 l F).budget kclk coef A a ha).capOf .sym n) ≤ _
    rw [← hCd]
    have := Nat.mul_le_mul_right (4096 * C) hnc
    omega
  -- the cap below `2^{(48+Z)L}`
  have hc : C ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l := by
    rw [hCd]; exact CallIndexR.cap_leR l F.cr .sym n
  have hcr := cr_le_k l F kclk coef A a ha hs
  have hkq : ((gate0 l F).budget kclk coef A a ha).kOf n ≤ n := hcall.2.2.2.2.2.2.kq
  have hK1 : CallIndexR.capK F.cr ≤ 2 ^ (48 * Nat.clog 2 (n + 2)) := by
    show (2 * F.cr + 2) ^ 48 ≤ _
    exact pow_mono_mul 48 (by omega)
  have hZ := pow_N_le n (CallIndexR.capZR l)
  have h3 : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.B ≤
      2 ^ (13 + (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := by
    refine hB.trans ?_
    calc 8192 * C ≤ 8192 * (2 ^ (48 * Nat.clog 2 (n + 2)) * 2 ^ (CallIndexR.capZR l * Nat.clog 2 (n + 2))) :=
          Nat.mul_le_mul_left _ (hc.trans (Nat.mul_le_mul hK1 hZ))
      _ = 2 ^ (13 + (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2)) := by
          rw [pow_add, show (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2) =
            48 * Nat.clog 2 (n + 2) + CallIndexR.capZR l * Nat.clog 2 (n + 2) by ring, pow_add]; norm_num
  have hJ : (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.J ≤
      13 + (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2) + 9 := by
    show Nat.clog 2 (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.B + 9 ≤ _
    have := Nat.clog_le_of_le_pow h3
    omega
  -- the ceiling square root
  obtain ⟨S, hSd⟩ : ∃ S, S = Nat.sqrt C := ⟨_, rfl⟩
  have h5 : CanonicalFourfoldRowProgram.natCeilSqrt
      (64 ^ 2 * (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).base.B) ≤ 5824 * (S + 1) := by
    apply SymSizes.natCeilSqrt_le_of
    have hs' : C < (S + 1) * (S + 1) := by rw [hSd]; exact Nat.lt_succ_sqrt C
    have e : 5824 * (S + 1) * (5824 * (S + 1)) = 33918976 * ((S + 1) * (S + 1)) := by ring
    rw [e]
    have := Nat.mul_le_mul_left (64 ^ 2) hB
    norm_num at this ⊢
    omega
  have h6 := lbP_lin (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
  unfold symDg symDD
  rw [← hCd, ← hSd]
  have eZ : (48 + CallIndexR.capZR l) * Nat.clog 2 (n + 2) =
      48 * Nat.clog 2 (n + 2) + CallIndexR.capZR l * Nat.clog 2 (n + 2) := by ring
  have eD : (780 * (48 + CallIndexR.capZR l) + 384 * F.filterErrDeg + 436876) * (S + Nat.clog 2 (n + 2)) =
      780 * 48 * S + 780 * (CallIndexR.capZR l * S) + 384 * (F.filterErrDeg * S) + 436876 * S +
        (780 * 48 * Nat.clog 2 (n + 2) + 780 * (CallIndexR.capZR l * Nat.clog 2 (n + 2)) +
          384 * (F.filterErrDeg * Nat.clog 2 (n + 2)) + 436876 * Nat.clog 2 (n + 2)) := by ring
  rw [eD]
  rw [eZ] at hJ
  exact max_le (by omega) (by omega)

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

end
