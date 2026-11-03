import Lean
import Proof.Wire_3_5.FinalPass.FreeGen9
import Proof.Wire_3_5.FinalPass.SymSz1Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SymFr3Base


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM free numbers (root #145 (ii)), part 4: the SYM constants and the pad and load bounds

At a SYM call the free numbers are `freeVal2 (symK2 c) (symX …)` (`FreeGen.freeProg2`): `m = max(8·nc + 16·a·W, 8)`
(the degenerate call's padded batch has one constant row, #146 (c′)), `Q' = dQ(2kh+β)`, `h = dH(n+1)^{eH}`,
`pr = dP(n+1)^{eP}` (P3:1886-1906; P3:1596-1615 for `h`), and the requests' degree bound is
`dF c x = dD·(⌊√B_S⌋ + β)`, the paper's `d_S = C_D(√B + L)` (P3:3094-3100).
* `SymC`, **`symK2`**, **`symDF`**;
* `kL_le_loadPsi` (`k + L ≤ ψ` once `C_D ≥ 1`, through `Ψ_aux`, P3:3101-3102);
* **`pad_sym2`** (`SymFreeOk4.pad_le`), `c3K2`, **`c3_sym2`** (`SymFreeOk4.c3_le` at `K3 = c3K2 c`, `D3 = eH + eP`).
Paper quantities of the main types: the pad `2^ρ` against `2^{n−k}poly(n)`, `h + Q' + m + pr` against `(ψ+1)·poly(n)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

section Gate
variable (l : Literals) (F : GateFree l)

/-- **The load bound** (`SymFreeOk4.c3_le` at `freeProg2 (symK2 c)`, `K3 = c3K2 c`, `D3 = eH + eP`). -/
theorem c3_sym2 (c : SymC) : 1 ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3 +
        (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 +
        (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 +
        (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5 ≤
        c3K2 c * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ (c.eH + c.eP) := by
  intro hCD kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hkL : ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) ≤
      ((gate0 l F).budget kclk coef A a ha).psiOf n := by
    unfold TimeBudget.psiOf
    exact kL_le_loadPsi _ _ _ _ _ hCD
  have hkh := kh_two l F kclk coef A a ha hs
  have hW : W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) ≤ Nat.clog 2 (n + 2) + 4 :=
    W_le _
  have hPH : (n + 1) ^ c.eH ≤ (n + 1) ^ (c.eH + c.eP) := Nat.pow_le_pow_right (by omega) (by omega)
  have hPP : (n + 1) ^ c.eP ≤ (n + 1) ^ (c.eH + c.eP) := Nat.pow_le_pow_right (by omega) (by omega)
  have hP1 : 1 ≤ (n + 1) ^ (c.eH + c.eP) := Nat.one_le_pow _ _ (by omega)
  show c.dH * (n + 1) ^ c.eH + c.dQ * (SeedFix.callKh _ + SeedFix.callKh _ + Nat.clog 2 (n + 2)) +
      max (8 * carriers.length + 16 * (a' * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) +
        0 * W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) + 0 * a' + 0 * (SymDec.cyOf Cs).sum + 0)
        8 + c.dP * (n + 1) ^ c.eP ≤ _
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ, ψ = ((gate0 l F).budget kclk coef A a ha).psiOf n := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) := ⟨_, rfl⟩
  rw [← hKd] at hkh hkL
  rw [← hLd] at hkL hW ⊢
  rw [← hψd] at hkL ⊢
  rw [← hwd] at hW ⊢
  obtain ⟨N, hNd⟩ : ∃ N, N = (n + 1) ^ (c.eH + c.eP) := ⟨_, rfl⟩
  rw [← hNd] at hPH hPP hP1 ⊢
  have haw : a' * w ≤ 4 * (L + 4) := Nat.mul_le_mul ha' hW
  have hm : max (8 * carriers.length + 16 * (a' * w) + 0 * w + 0 * a' + 0 * (SymDec.cyOf Cs).sum + 0) 8 ≤
      400 * (ψ + 1) := by
    simp only [Nat.zero_mul, Nat.add_zero]
    apply max_le <;> omega
  have t1 : c.dH * (n + 1) ^ c.eH ≤ c.dH * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans hPH (Nat.le_mul_of_pos_left _ (by omega)))
  have t2 : c.dP * (n + 1) ^ c.eP ≤ c.dP * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans hPP (Nat.le_mul_of_pos_left _ (by omega)))
  have t3 : c.dQ * (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + L) ≤ c.dQ * ((ψ + 1) * N) :=
    Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.le_mul_of_pos_right _ hP1))
  have t4 : 400 * (ψ + 1) ≤ 400 * ((ψ + 1) * N) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hP1)
  have e : c3K2 c * (ψ + 1) * N = c.dH * ((ψ + 1) * N) + c.dQ * ((ψ + 1) * N) + 400 * ((ψ + 1) * N) +
      c.dP * ((ψ + 1) * N) := by unfold c3K2; ring
  rw [e]
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

end
