import Lean
import Proof.Wire_3_5.FinalPass.SymFr3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.FinalPass.SymSz2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SymHrBase


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM free numbers (root #145 (ii)), part 5: the exact recovery range `hrange`

"Suppose `0 ≤ V(z) ≤ J` on every column, choose `Q ≥ 1` with `2^Q > J`, and put `Q' = Q+m−1`" (alg:compiler,
P3:1886-1890) and "`V_p(z) ≤ 2^{8ℓ−|p|}·|T|·N^8(QN²)^8`" (samp:range, P3:2919-2921): the child's scaled value
`2^{m−1}·V_p(z)` is below `2^{Q'}` once `Q'` exceeds `m + 8ℓ + 24kh + log|T| + 8 log Q`.
* **`sampElim_lt`** (generic in the seed parameters and the state type);
* `cS`, **`hrange_sym`**: at a SYM call, `Q' = dQ(2kh+β)` with `dQ ≥ cS + 401` (`cS = 16eQ + eN + 40`).
Paper quantity of the main type: the exact recovery range of the child's printed objective. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.Sampler

/-- The exponent of the child's value at a SYM call (in units of `k + L`). -/
noncomputable def cS (l : Literals) (fe : ℕ) : ℕ := 16 * eQ l fe + eN l fe + 40

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`hrange` at a SYM call** (`SymEAt3`'s range clause) at `freeProg2 (symK2 c)`, `dQ ≥ cS + 401`. -/
theorem hrange_sym (c : SymC) (hdQ : cS l F.filterErrDeg + 401 ≤ c.dQ) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ∀ p' : List Bool, p'.length ≤ 8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 - 1) *
        SeedFix.sampElim (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
          (SeedFix.symStateBits (callInputs l F kclk coef A a ha) hs Cs carriers translation z) p'.length
          (SeedFix.listNum p') <
        2 ^ (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 := by
  intro p' hp' z
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hNT := symNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := symCount_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl := ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hcard : Fintype.card (SeedFix.SymIndex (callInputs l F kclk coef A a ha) hs Cs carriers) =
      Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers := by
    rw [Fintype.card_congr (Enum.symIndexEquiv (callInputs l F kclk coef A a ha) hs Cs carriers), Fintype.card_fin]
  have hW : W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) ≤ Nat.clog 2 (n + 2) + 4 :=
    W_le _
  have hL1 := one_le_L n
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hNT hQ hl
  rw [← hKd] at hkh
  rw [← hLd] at hW hL1
  have v4 : (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 ≤
      400 * (K + L) := by
    show max (mOf (symK2 c).k (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) 8 ≤ _
    unfold mOf
    obtain ⟨w, hwd⟩ : ∃ w, w = W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) := ⟨_, rfl⟩
    rw [← hwd] at hW ⊢
    have haw : a' * w ≤ 4 * (L + 4) := Nat.mul_le_mul ha' hW
    show max (8 * carriers.length + 16 * (a' * w) + 0 * w + 0 * a' + 0 * (SymDec.cyOf Cs).sum + 0) 8 ≤ _
    simp only [Nat.zero_mul, Nat.add_zero]
    apply max_le <;> omega
  have v2 : (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 =
      c.dQ * (K + L) := by
    show c.dQ * (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2)) = _
    rw [← hLd]
    have e0 : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
        SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + L = K + L := by omega
    rw [e0]
  refine sampElim_lt _ _ _ _ hp' _ _ (eN l F.filterErrDeg * (K + L)) (eQ l F.filterErrDeg * (K + L))
    (by rw [hcard]; exact hNT) hQ ?_
  rw [v2]
  have hdq : (cS l F.filterErrDeg + 401) * (K + L) ≤ c.dQ * (K + L) := Nat.mul_le_mul_right _ hdQ
  have hl' : 8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell ≤
      8 * ((eQ l F.filterErrDeg + 2) * (K + L)) := Nat.mul_le_mul_left _ hl
  have hkh' : (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).kh =
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) := rfl
  have e2 : (cS l F.filterErrDeg + 401) * (K + L) = 16 * (eQ l F.filterErrDeg * (K + L)) +
      eN l F.filterErrDeg * (K + L) + 441 * (K + L) := by unfold cS; ring
  have e3 : 8 * ((eQ l F.filterErrDeg + 2) * (K + L)) = 8 * (eQ l F.filterErrDeg * (K + L)) + 16 * (K + L) := by ring
  have hKL : 1 ≤ K + L := by omega
  rw [hkh']
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

end
