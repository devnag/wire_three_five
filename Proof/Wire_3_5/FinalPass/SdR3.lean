import Proof.Wire_3_5.FinalPass.SdR2

/-! # S4 v2, part R3: the call's sizes below `X = KX·(n+2)^{ZX}` with `ZX` on `(l, fe)` (P3:3170-3178)

S4 v1's `Sd.ZX` carries `CallIndex.capZ l F ∋ 51·c_r`. Here **`ZX`** is built from `CallIndexR`'s exponents
(`capZR l`, `gapZR l fe`, the width's `ZT l F` and `ZV l` of part R2, the size polynomials' degrees) and **`KX`** absorbs
`c_r` (`capK`, `gapK`, `flatK`): **`Xf`**, `xlift`, `hKX`, **`atoms_of`** (the cap through `cap_leR`, the seeds through
`gapSeed_leR`), `x_vsym`, `x_vthr`, `x_T`, `x_ssz`, `x_sfn`, `x_tfn` (the statements of v1 at the new constants).
Namespace `Sd.R`: S4 v2's names shadow v1's; the generic lemmas (`lift`, `poly_comp`, `AtomsX`, `SymSizeOK`,
`ThrSizeOK`, …) are v1's.

Paper quantity of the main type: the call's sizes, polynomial in `n` with the powers fixed before the gate
(P3:3114-3115, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd.R
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 symCallOf thrCallOf thrWords thrNums)

section Family
variable (l : Literals) (F : GateFree l)

/-- The polynomial `X`'s exponent. -/
noncomputable def ZX (E : SymPtEval2) (Dsz Dtz : ℕ) : ℕ :=
  52 + PrimAsm.CallIndexR.gapZR l F.filterErrDeg + PrimAsm.CallIndexR.capZR l + ZV l + Dsz * (E.D + 1) +
    Dtz * (ThrPt.thrPtProg.D + 1) + ZT l F

/-- The polynomial `X`'s coefficient. -/
noncomputable def KX (E : SymPtEval2) (Csz Ctz : ℕ) : ℕ :=
  1000 + 771 * (F.filterErrDeg + 1) + Csz + Ctz + (E.C + 1) * (Csz + 1) ^ E.D +
    (ThrPt.thrPtProg.C + 1) * (Ctz + 1) ^ ThrPt.thrPtProg.D + KT l F + PrimAsm.CallIndexR.capK F.cr +
    PrimAsm.CallIndexR.gapK F.cr + 2 * PrimAsm.CallIndexR.flatK F.cr

/-- **The sizes' polynomial** `X = KX·(n+2)^{ZX}`. -/
noncomputable def Xf (E : SymPtEval2) (Csz Dsz Ctz Dtz n : ℕ) : ℕ := KX l F E Csz Ctz * (n + 2) ^ ZX l F E Dsz Dtz

variable (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

variable (E : SymPtEval2) (Csz Dsz Ctz Dtz : ℕ)

theorem xlift {q c z n : ℕ} (hq : q ≤ c * (n + 2) ^ z) (hc : c ≤ KX l F E Csz Ctz) (hz : z ≤ ZX l F E Dsz Dtz) :
    q ≤ Xf l F E Csz Dsz Ctz Dtz n :=
  lift (by omega) hq hc hz

theorem hKX : 1000 + 771 * (F.filterErrDeg + 1) + Csz + Ctz + (E.C + 1) * (Csz + 1) ^ E.D +
    (ThrPt.thrPtProg.C + 1) * (Ctz + 1) ^ ThrPt.thrPtProg.D + KT l F + PrimAsm.CallIndexR.capK F.cr +
    PrimAsm.CallIndexR.gapK F.cr + 2 * PrimAsm.CallIndexR.flatK F.cr ≤ KX l F E Csz Ctz := le_rfl

/-- **The call's sizes below `X`.** -/
theorem atoms_of (m : Mode) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) (carriers : List (Carrier n))
    (henv : ∀ X ∈ carriers, Carrier.WithinEnvelope 26 X) (hcar : carriers.length ≤ 2) :
    AtomsX ((callInputs l F kclk coef A a ha).starParams n hs) carriers
      ((callInputs l F kclk coef A a ha).filterParams m n) (Xf l F E Csz Dsz Ctz Dtz n) := by
  have K := hKX l F E Csz Ctz
  have hZ : 52 + PrimAsm.CallIndexR.gapZR l F.filterErrDeg + PrimAsm.CallIndexR.capZR l ≤ ZX l F E Dsz Dtz := by
    unfold ZX; omega
  have hN : 1 ≤ n + 2 := by omega
  have herr : ((callInputs l F kclk coef A a ha).filterParams m n).errExp + 1 ≤ (F.filterErrDeg + 1) * (n + 2) := by
    have e : ((callInputs l F kclk coef A a ha).filterParams m n).errExp = F.filterErrDeg * Nat.clog 2 (n + 2) := rfl
    have := Nat.mul_le_mul_left F.filterErrDeg (clog_le (n + 2))
    rw [e, Nat.add_mul, one_mul]
    omega
  have hcl : ∀ k, Seams.carLen carriers k ≤ 2 * (n + 2) ^ 26 := fun k =>
    (carLen_le carriers henv k).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 26))
  have hmask : ∀ k (hk : k < carriers.length), (maskGates (carriers.get ⟨k, hk⟩)).length ≤ 2 * (n + 2) ^ 26 :=
    fun k hk => by
      have := hcl k
      unfold Seams.carLen at this
      rw [dif_pos hk] at this
      exact this
  have hhof : ∀ k, Hof carriers k ≤ 35 * (n + 2) ^ 52 := fun k => (Hof_le carriers henv k).trans (hof35 n)
  refine
    { n2 := xlift l F E Csz Dsz Ctz Dtz (c := 1) (z := 1) (by rw [pow_one, one_mul]; exact le_rfl) (by omega) (by omega)
      len := xlift l F E Csz Dsz Ctz Dtz (c := 2) (z := 26)
        (show 2 * (n + 1) ^ 26 ≤ 2 * (n + 2) ^ 26 from Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 26))
        (by omega) (by omega)
      cap := xlift l F E Csz Dsz Ctz Dtz (c := PrimAsm.CallIndexR.capK F.cr) (z := PrimAsm.CallIndexR.capZR l)
        (PrimAsm.CallIndexR.cap_leR l F.cr m n) (by omega) (by omega)
      err := xlift l F E Csz Dsz Ctz Dtz (c := F.filterErrDeg + 1) (z := 1) (by rw [pow_one]; exact herr)
        (by omega) (by omega)
      G := xlift l F E Csz Dsz Ctz Dtz (c := PrimAsm.CallIndexR.gapK F.cr) (z := PrimAsm.CallIndexR.gapZR l F.filterErrDeg)
        (PrimAsm.CallIndexR.gapSeed_leR l F kclk coef A a ha m n) (by omega) (by omega)
      car2 := hcar
      cl := fun k => xlift l F E Csz Dsz Ctz Dtz (hcl k) (by omega) (by omega)
      hof := fun k => xlift l F E Csz Dsz Ctz Dtz (hhof k) (by omega) (by omega)
      tabH := fun k hk => by
        have h1 := hhof ⟨k, lt_of_lt_of_le hk hcar⟩
        rw [hof_get carriers k hk (lt_of_lt_of_le hk hcar)] at h1
        exact xlift l F E Csz Dsz Ctz Dtz h1 (by omega) (by omega)
      mask := fun k hk => xlift l F E Csz Dsz Ctz Dtz (hmask k hk) (by omega) (by omega)
      tbl := fun e k hk => xlift l F E Csz Dsz Ctz Dtz (c := 771 * (F.filterErrDeg + 1)) (z := 27)
        (tbl771 _ e _ n _ herr (hmask k hk)) (by omega) (by omega) }

theorem x_vsym (n : ℕ) {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hcar : carriers.length ≤ 2) :
    Fintype.card (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed ≤
      Xf l F E Csz Dsz Ctz Dtz n :=
  xlift l F E Csz Dsz Ctz Dtz (vsym_le l F kclk coef A a ha n ha' Cs carriers hd hcar)
    (by have := hKX l F E Csz Ctz; omega) (by unfold ZX; omega)

theorem x_vthr (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    Fintype.card (ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg) *
        Fintype.card (PrimeIndex (thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
          (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) ≤ Xf l F E Csz Dsz Ctz Dtz n :=
  xlift l F E Csz Dsz Ctz Dtz (vthr_le l F kclk coef A a ha n hs ha' Cs hd)
    (by have := hKX l F E Csz Ctz; omega) (by unfold ZX; omega)

theorem x_T (r : FReq l F kclk coef A a ha) : Tf l F kclk coef A a ha r ≤ Xf l F E Csz Dsz Ctz Dtz r.1.n :=
  xlift l F E Csz Dsz Ctz Dtz (c := KT l F) (z := ZT l F) le_rfl
    (by have := hKX l F E Csz Ctz; omega) (by unfold ZX; omega)

theorem x_ssz (hS : SymSizeOK l F kclk coef A a ha E Csz Dsz) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hcar : carriers.length ≤ 2) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    symSize E (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) ≤ Csz * (n + 2) ^ Dsz :=
  (hS n hs ha' Cs carriers hcar hd).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem x_sfn (hS : SymSizeOK l F kclk coef A a ha E Csz Dsz) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (hcar : carriers.length ≤ 2) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    symSize E (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) ≤ Xf l F E Csz Dsz Ctz Dtz n ∧
    E.need (symSize E (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers)) + 1 ≤
      Xf l F E Csz Dsz Ctz Dtz n ∧
    E.bound (symSize E (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers)) + 1 ≤
      Xf l F E Csz Dsz Ctz Dtz n := by
  have h := x_ssz l F kclk coef A a ha E Csz Dsz hS n hs ha' Cs carriers hcar hd
  have K := hKX l F E Csz Ctz
  have hZ1 : Dsz ≤ ZX l F E Dsz Dtz := by
    unfold ZX; have := Nat.le_mul_of_pos_right Dsz (show 0 < E.D + 1 by omega); omega
  have hZ2 : Dsz * E.D ≤ ZX l F E Dsz Dtz := by
    unfold ZX; have := Nat.mul_le_mul_left Dsz (show E.D ≤ E.D + 1 by omega); omega
  refine ⟨xlift l F E Csz Dsz Ctz Dtz h (by omega) hZ1, ?_, ?_⟩
  · exact xlift l F E Csz Dsz Ctz Dtz (poly_comp E.C E.D Csz Dsz (n + 2) _ _ (E.need_le _) h (by omega))
      (by omega) hZ2
  · exact xlift l F E Csz Dsz Ctz Dtz (poly_comp E.C E.D Csz Dsz (n + 2) _ _ (E.bound_le _) h (by omega))
      (by omega) hZ2

theorem x_tfn (hT : ThrSizeOK l F kclk coef A a ha Ctz Dtz) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    {a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcar : carriers.length ≤ 2) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    ThrPt.thrSize (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers translation) ≤
      Xf l F E Csz Dsz Ctz Dtz n ∧
    ThrPt.thrPtProg.need (ThrPt.thrSize (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers
      translation)) + 1 ≤ Xf l F E Csz Dsz Ctz Dtz n ∧
    ThrPt.thrPtProg.bound (ThrPt.thrSize (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs
      carriers translation)) + 1 ≤ Xf l F E Csz Dsz Ctz Dtz n := by
  have h := (hT n hs ha' Cs carriers translation hcar hd).trans
    (Nat.mul_le_mul_left Ctz (Nat.pow_le_pow_left (show n + 1 ≤ n + 2 by omega) Dtz))
  have K := hKX l F E Csz Ctz
  have hZ1 : Dtz ≤ ZX l F E Dsz Dtz := by
    unfold ZX; have := Nat.le_mul_of_pos_right Dtz (show 0 < ThrPt.thrPtProg.D + 1 by omega); omega
  have hZ2 : Dtz * ThrPt.thrPtProg.D ≤ ZX l F E Dsz Dtz := by
    unfold ZX; have := Nat.mul_le_mul_left Dtz (show ThrPt.thrPtProg.D ≤ ThrPt.thrPtProg.D + 1 by omega); omega
  refine ⟨xlift l F E Csz Dsz Ctz Dtz h (by omega) hZ1, ?_, ?_⟩
  · exact xlift l F E Csz Dsz Ctz Dtz
      (poly_comp ThrPt.thrPtProg.C ThrPt.thrPtProg.D Ctz Dtz (n + 2) _ _ (ThrPt.thrPtProg.need_le _) h (by omega))
      (by omega) hZ2
  · exact xlift l F E Csz Dsz Ctz Dtz
      (poly_comp ThrPt.thrPtProg.C ThrPt.thrPtProg.D Ctz Dtz (n + 2) _ _ (ThrPt.thrPtProg.bound_le _) h (by omega))
      (by omega) hZ2

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd.R
