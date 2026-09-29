import Proof.Wire_3_5.FinalPass.SymOcc3

/-! # The printer's gate budget at a SYM call, part 4: `occ_sym`

The clause `(2·occBound)² ≤ ⌈(2^{dRow})^{1/10}⌉` of `C3Req.Pre` at the SYM child request of every prefix
(alg:eq-budget, P3:1897-1900), from the call's fit (`c_ψ·ψ ≤ n`), the floors (`occCD ≤ C_D`, `1 ≤ c_ψ`;
P3:3094-3107) and the child expression's term count `A ≤ 2^{A₁(k+L)}`.
* `m_le`, `Qp_eq`, **`occ_sym`**.
Paper quantity of the main type: alg:eq-budget at a SYM call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

section Gate
variable (l : Literals) (F : GateFree l)

/-- `m ≤ 400(k+L)` at a SYM call. -/
theorem m_le (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 ≤
      400 * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
  have hnc : carriers.length ≤ 2 := hcall.2.2.2.1
  have hW : W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) ≤ Nat.clog 2 (n + 2) + 4 :=
    W_le _
  have hL1 := one_le_L n
  show max (mOf (symK2 c).k (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs)) 8 ≤ _
  unfold mOf
  obtain ⟨w, hwd⟩ : ∃ w, w = W (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) := ⟨_, rfl⟩
  rw [← hwd] at hW ⊢
  have haw : a' * w ≤ 4 * (Nat.clog 2 (n + 2) + 4) := Nat.mul_le_mul ha' hW
  show max (8 * carriers.length + 16 * (a' * w) + 0 * w + 0 * a' + 0 * (SymDec.cyOf Cs).sum + 0) 8 ≤ _
  simp only [Nat.zero_mul, Nat.add_zero]
  apply max_le <;> omega

/-- `Q' = dQ(k+L)` at a SYM call. -/
theorem Qp_eq (c : SymC) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 =
      c.dQ * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)) := by
  have hkh := kh_two l F kclk coef A a ha hs
  show c.dQ * (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
    SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2)) = _
  have e0 : SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) +
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + Nat.clog 2 (n + 2) =
      ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) := by omega
  rw [e0]

/-- **The printer's budget at the SYM child request of every prefix** under the floors. -/
theorem occ_sym (c : SymC) (A1 : ℕ) (hCD : occCD (gate0 l F).alg c A1 ≤ F.CD) (hcpsi : 1 ≤ F.E.cpsi)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (nT Rn : ℕ) (batch : List SeedFix.SExpr) (p' : List Bool)
    (hV : (SeedFix.sampTerms (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers) nT Rn batch
      p'.length (SeedFix.listNum p')).length ≤
        2 ^ (A1 * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)))) :
    (2 * (PrimT.C4Child.chR (PrimT.C4Sym.symR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
      (symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5) 0)
      (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers) nT Rn batch p').occBound
        (gate0 l F).alg) *
    (2 * (PrimT.C4Child.chR (PrimT.C4Sym.symR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4)
      (symDF c (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs))
      ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5) 0)
      (PrimT.C4Val.symSP (callInputs l F kclk coef A a ha) hs Cs carriers) nT Rn batch p').occBound
        (gate0 l F).alg) ≤
      SourceInterfaces.rectangularInnerDimension (2 ^ PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs)) := by
  have hm := m_le l F c kclk coef A a ha ha' Cs carriers translation hcall hs
  have hQ := Qp_eq l F c kclk coef A a ha Cs carriers hs
  have hD := symD_le l F kclk coef A a ha ha' Cs carriers translation hcall hs
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3)
    ((freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2) 0
  have hfits := hcall.2.2.2.2.2.2.pre
  have hkL := kL_mul_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hsy := loadSym_le F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
    (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
  have hdr := two_dRow_ge ((callInputs l F kclk coef A a ha).starParams n hs)
  have hL1 := one_le_L n
  refine SampShape.occ_of (gate0 l F).alg _ (A1 * (((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2)))
    (((gate0 l F).budget kclk coef A a ha).kOf n + cDa (gate0 l F).alg * Nat.clog 2 (n + 2)) hV hD ?_
  have hψ : ((gate0 l F).budget kclk coef A a ha).psiOf n = loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n)
      (Nat.clog 2 (n + 2)) (((gate0 l F).budget kclk coef A a ha).capOf .thr n)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := rfl
  rw [← hψ] at hkL hsy
  have hcp : 1 ≤ (gate0 l F).E.cpsi := hcpsi
  have hn : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤ n := by
    have : ((gate0 l F).budget kclk coef A a ha).psiOf n ≤
        (gate0 l F).E.cpsi * ((gate0 l F).budget kclk coef A a ha).psiOf n := Nat.le_mul_of_pos_left _ hcp
    exact this.trans (le_trans (Nat.le_add_right _ _) hfits)
  obtain ⟨K, hKd⟩ : ∃ K, K = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, L = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ, ψ = ((gate0 l F).budget kclk coef A a ha).psiOf n := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S, S = Nat.sqrt (((gate0 l F).budget kclk coef A a ha).capOf .sym n) := ⟨_, rfl⟩
  obtain ⟨m4, hm4d⟩ : ∃ m, m = (freeProg2 (symK2 c)).val (PrimT.C4SymW.symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 := ⟨_, rfl⟩
  obtain ⟨dR, hdRd⟩ : ∃ d, d = PrimT.C4Geo.dRow ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  have hdr' : n - K ≤ 2 * dR := by rw [hKd, hdRd]; exact hdr
  rw [← hKd, ← hLd] at hm hkL hsy hQ
  rw [← hψd] at hkL hsy hn
  rw [← hSd] at hsy
  rw [← hm4d] at hm
  have hCD1 : 2 ≤ F.CD := by unfold occCD at hCD; omega
  have hC1 : 160 * (A1 + 400 + c.dQ + 1) ≤ F.CD := by unfold occCD at hCD; omega
  have hC2 : 160 * (c.dQ * c.dD * cDa (gate0 l F).alg) ≤ F.CD * F.CD := by
    unfold occCD at hCD
    have : F.CD ≤ F.CD * F.CD := Nat.le_mul_self _
    omega
  have hcDa : 1 ≤ cDa (gate0 l F).alg := by unfold cDa; omega
  -- the linear part
  have hA : F.CD * (A1 * (K + L) + m4 + c.dQ * (K + L) + 1) ≤ (A1 + 400 + c.dQ + 1) * ψ := by
    have h1 : A1 * (K + L) + m4 + c.dQ * (K + L) + 1 ≤ (A1 + 400 + c.dQ + 1) * (K + L) := by
      have e : (A1 + 400 + c.dQ + 1) * (K + L) = A1 * (K + L) + 400 * (K + L) + c.dQ * (K + L) + (K + L) := by ring
      omega
    calc F.CD * (A1 * (K + L) + m4 + c.dQ * (K + L) + 1) ≤ F.CD * ((A1 + 400 + c.dQ + 1) * (K + L)) :=
          Nat.mul_le_mul_left _ h1
      _ = (A1 + 400 + c.dQ + 1) * (F.CD * (K + L)) := by ring
      _ ≤ (A1 + 400 + c.dQ + 1) * ψ := Nat.mul_le_mul_left _ hkL
  -- the quadratic part
  have hB : F.CD * F.CD * (c.dQ * (K + L) * (c.dD * (S + L)) * (K + cDa (gate0 l F).alg * L)) ≤
      (c.dQ * c.dD * cDa (gate0 l F).alg) * ψ := by
    have h1 : K + cDa (gate0 l F).alg * L ≤ cDa (gate0 l F).alg * (K + L) := by
      have := Nat.mul_le_mul_right K hcDa
      have e : cDa (gate0 l F).alg * (K + L) = cDa (gate0 l F).alg * K + cDa (gate0 l F).alg * L := by ring
      omega
    calc F.CD * F.CD * (c.dQ * (K + L) * (c.dD * (S + L)) * (K + cDa (gate0 l F).alg * L))
        ≤ F.CD * F.CD * (c.dQ * (K + L) * (c.dD * (S + L)) * (cDa (gate0 l F).alg * (K + L))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = (c.dQ * c.dD * cDa (gate0 l F).alg) * (F.CD * F.CD * ((K + L) * (K + L) * (S + L))) := by ring
      _ ≤ (c.dQ * c.dD * cDa (gate0 l F).alg) * ψ := Nat.mul_le_mul_left _ hsy
  have hk2 : 2 * K ≤ ψ := by
    have : 2 * (K + L) ≤ F.CD * (K + L) := Nat.mul_le_mul_right _ hCD1
    omega
  have key := occ_num ψ n K dR F.CD (A1 * (K + L) + m4 + c.dQ * (K + L))
    (c.dQ * (K + L) * (c.dD * (S + L)) * (K + cDa (gate0 l F).alg * L)) (A1 + 400 + c.dQ + 1)
    (c.dQ * c.dD * cDa (gate0 l F).alg) (by omega) hA hB hC1 hC2 hn hk2 hdr'
  rw [← hQ] at key
  rw [hKd, hLd, hSd, hm4d, hdRd] at key
  exact key

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

