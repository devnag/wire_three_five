import Lean
import Proof.Wire_3_5.FinalPass.SymHp1
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymOcc4
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.FinalPass.SymSz2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SymOcc3Base


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM child request's precondition, part 2: coefficients, pool fits, term count

* **`coef_sym`**: `N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}` (the child's coefficients `(−N²)^{|β|}·count`, P3:2950-2957);
* **`fits_sym`**: `CoefFit`, `PNFit`, `DenseFit` at `h = dH(n+1)^{eH}` (alg:disjoint's bits, P3:1596-1615);
* `A1`, **`lenV_sym`**: the child expression has `≤ 2^{A₁(k+L)}` terms (rows of `≤ 2^{eT(k+L)}` terms, `R ≤ 10`).
Paper quantities of the main types: the child request's `b`, the pool's fields against `h`, and `A`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- The term-count exponent. -/
noncomputable def A1 (l : Literals) (fe eT : ℕ) : ℕ := eN l fe + 4 + 8 * (eQ l fe + 2) + 8 + 80 * eT

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}`** at a SYM call. -/
theorem coef_sym (c : SymC) (hdP : 2 * (24 + 8 * eQ l F.filterErrDeg + c.dQ) ≤ c.dP) (heP : 1 ≤ c.eP)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 16 *
        2 ^ (8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell) *
        2 ^ (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 ≤
      2 ^ (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5 := by
  have hQ := Qp_eq l F c kclk coef A a ha Cs carriers hs
  have hkL := kL_le_n l F kclk coef A a ha ha' Cs carriers translation hcall
  have hl := ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hN : (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 16 =
      2 ^ (8 * ((gate0 l F).budget kclk coef A a ha).kOf n) := by
    show (2 ^ SeedFix.callKh _) ^ 16 = _
    rw [← pow_mul]; congr 1; omega
  rw [hN, hQ, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  show _ ≤ c.dP * (n + 1) ^ c.eP
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hkL hl ⊢
  have h1 : (n + 1) ≤ (n + 1) ^ c.eP := Nat.le_self_pow (by omega) _
  have h2 : 8 * (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell ≤
      8 * ((eQ l F.filterErrDeg + 2) * (K + L)) := Nat.mul_le_mul_left _ hl
  have h3 : (24 + 8 * eQ l F.filterErrDeg + c.dQ) * (K + L) ≤ (24 + 8 * eQ l F.filterErrDeg + c.dQ) * (2 * (n + 1)) :=
    Nat.mul_le_mul_left _ hkL
  have h4 : (2 * (24 + 8 * eQ l F.filterErrDeg + c.dQ)) * (n + 1) ≤ c.dP * (n + 1) ^ c.eP :=
    Nat.mul_le_mul hdP h1
  have e1 : (24 + 8 * eQ l F.filterErrDeg + c.dQ) * (K + L) = 24 * (K + L) + 8 * (eQ l F.filterErrDeg * (K + L)) +
      c.dQ * (K + L) := by ring
  have e2 : 8 * ((eQ l F.filterErrDeg + 2) * (K + L)) = 8 * (eQ l F.filterErrDeg * (K + L)) + 16 * (K + L) := by ring
  have e3 : (24 + 8 * eQ l F.filterErrDeg + c.dQ) * (2 * (n + 1)) =
      (2 * (24 + 8 * eQ l F.filterErrDeg + c.dQ)) * (n + 1) := by ring
  omega

/-- **The pool's three fits** at a SYM call (`h = dH(n+1)^{eH}`). -/
theorem fits_sym (c : SymC) (hdH : (gate0 l F).alg.coefficient * 4 ^ (gate0 l F).alg.degree + 2 ≤ c.dH)
    (heH : 26 * (gate0 l F).alg.degree + 1 ≤ c.eH) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Q psi : ℕ) :
    Pool.CoefFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (Records.symPool Cs carriers)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3) Q psi) ∧
      Req.PNFit (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (Records.symPool Cs carriers)
        ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3) Q psi) ∧
      Req.DenseFit ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
        (Pool.densePool (gate0 l F).alg
          (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
            (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation)
            (Records.symPool Cs carriers)
            ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3) Q psi).gates
          (PrimT.C4Geo.side ((callInputs l F kclk coef A a ha).starParams n hs))
          (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams n hs))
          (PrimT.C4Geo.flips ((callInputs l F kclk coef A a ha).starParams n hs)
            (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation))) := by
  have hcar : ∀ X ∈ carriers, X.WithinEnvelope 26 := hcall.2.1
  have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := fun i => hcall.2.2.1 i
  have hB := sym_budget_le (gate0 l F).alg Cs carriers hcar hd
  have hb := symBud_le (gate0 l F).alg n
  refine PoolFit.poolFits_of (gate0 l F).alg (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a ha).starParams n hs)
    (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) (Records.symPool Cs carriers)
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3) Q psi)
    (symBud (gate0 l F).alg n) hB ?_
  show symBud (gate0 l F).alg n + n + 2 ≤ c.dH * (n + 1) ^ c.eH
  refine hb.trans (Nat.mul_le_mul hdH (Nat.pow_le_pow_right (by omega) heH))

/-- **The child expression has `≤ 2^{A₁(k+L)}` terms** at a SYM call (rows of `≤ T ≤ 2^{eT(k+L)}` terms, `R ≤ 10`). -/
theorem lenV_sym (eT T : ℕ) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (Rn : ℕ) (hRn : Rn ≤ 10) (batch : List SeedFix.SExpr)
    (hb : ∀ V ∈ batch, V.length ≤ T) (hT : T ≤ 2 ^ (eT * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))))
    (plen pre : ℕ) :
    (SeedFix.sampTerms (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
      (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn batch plen pre).length ≤
      2 ^ (A1 l F.filterErrDeg eT * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2))) := by
  have h0 := SampShape.length_sampTerms_leT (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers)
    (Enum.symNT (callInputs l F kclk coef A a ha) hs Cs carriers) Rn batch plen pre T hb
  have hNT := symNT_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hl := ell_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := kh_two l F kclk coef A a ha hs
  have hL1 := one_le_L n
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  rw [← hKd, ← hLd] at hNT hl hT ⊢
  rw [← hKd] at hkh
  rw [← hLd] at hL1
  have hN8 : (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).N ^ 8 ≤ 2 ^ (4 * (K + L)) := by
    show (2 ^ SeedFix.callKh _) ^ 8 ≤ _
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hl8 : (2 ^ (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers).ell) ^ 8 ≤
      2 ^ (8 * (eQ l F.filterErrDeg + 2) * (K + L)) := by
    rw [← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := Nat.mul_le_mul_right 8 hl
    have e : 8 * (eQ l F.filterErrDeg + 2) * (K + L) = (eQ l F.filterErrDeg + 2) * (K + L) * 8 := by ring
    omega
  have h28 : 2 ^ 8 ≤ 2 ^ (8 * (K + L)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT8 : T ^ (8 * Rn) ≤ 2 ^ (80 * eT * (K + L)) := by
    calc T ^ (8 * Rn) ≤ (2 ^ (eT * (K + L))) ^ (8 * Rn) := Nat.pow_le_pow_left hT _
      _ = 2 ^ (eT * (K + L) * (8 * Rn)) := by rw [← pow_mul]
      _ ≤ 2 ^ (80 * eT * (K + L)) := Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.mul_le_mul_left (eT * (K + L)) (show 8 * Rn ≤ 80 by omega)
          have e : 80 * eT * (K + L) = eT * (K + L) * 80 := by ring
          omega)
  refine h0.trans ?_
  calc _ ≤ 2 ^ (eN l F.filterErrDeg * (K + L)) * (2 ^ (4 * (K + L)) *
        (2 ^ (8 * (eQ l F.filterErrDeg + 2) * (K + L)) * (2 ^ (8 * (K + L)) * 2 ^ (80 * eT * (K + L))))) :=
        Nat.mul_le_mul hNT (Nat.mul_le_mul hN8 (Nat.mul_le_mul hl8 (Nat.mul_le_mul h28 hT8)))
    _ = 2 ^ (A1 l F.filterErrDeg eT * (K + L)) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; unfold A1; ring

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

end
