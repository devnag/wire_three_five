import Lean
import Proof.Wire_3_5.FinalPass.S6Iface
import Proof.Wire_3_5.FinalPass.SymFr3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.AssemblyDock3
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.S6FitBase


noncomputable section
set_option maxRecDepth 4096


/-! # S6: the final pass's constants `E₅`, `CD₅`, `c₅` and their `fits`

`S6Target := S6Uni → S6Out` (the S6Iface) from the uniformity bundle and the three request-size bounds (N1–N3 of
the #210 satisfiability check, produced by C6b; statements verbatim as sent 18:5x):

* **`FpInBound`** (N1): `|fpIn r| + 1 ≤ K_in·2^k·(n+1)^{D_in}`; **`SeedCountBound`** (N2): `|E| ≤ K_e·(n+1)^{D_e}`;
  **`PtCountBound`** (N3): `ptCount r ≤ K_p·2^{n−⌊k/4⌋}·(n+1)^{D_q}` (exponents chosen before `F`, coefficients after);
* the ℕ bookkeeping `pow_base_le`, `s5_le`, `out_le`, `pre_into`, `main_into`, and **`fits_arith`** (the whole
  residual at explicit atoms);
* `e5` (the envelope: `cpsi = 2D_g + D_g²`, `Apre = D_e + D_in·D_g + D_in·D_g²`, `Amain = D_q + D_g`), `c5v`,
  **`s6_fits`** (`S6Fits` at `E₅ = e5 …` fixed before `F`, `CD₅ = 1`, `c₅ = c5v …` after `F`) and **`s6Target`**.

The front, table, overhead and out-machine terms land in the preprocessing class `2^{cpsi·Ψ}·n^{Apre}` through `k ≤ Ψ`
(`kL_le_loadPsi` at `C_D ≥ 1 = CD₅`); the point term lands in the main pass `2^{n−k/4}·n^{Amain}`.

Paper quantity of the main type: `c₅`, `E₅` and the final pass's running time within `c₅·finalClasses E₅`
(prim:runtime, P3:3105-3115, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S6Fit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.Assembly

/-! ## The three request-size bounds (N1–N3) -/

section Sizes
variable (l : Literals)

/-- **N1**: the final pass's input length. -/
def FpInBound : Prop := ∀ fe : ℕ, ∃ Din : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ∃ Kin : ℕ,
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
      (fpIn l F kclk coef A a ha r).length + 1 ≤
        Kin * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf r.1.n) * (r.1.n + 1) ^ Din

/-- **N2**: the number of filter seeds. -/
def SeedCountBound : Prop := ∀ fe : ℕ, ∃ De : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ∃ Ke : ℕ,
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
      seedCount l F kclk coef A a ha r ≤ Ke * (r.1.n + 1) ^ De

/-- **N3**: the number of point evaluations, in the main pass's shape. -/
def PtCountBound : Prop := ∀ fe : ℕ, ∃ Dq : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ∃ Kp : ℕ,
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
      ptCount l F kclk coef A a ha r ≤
        Kp * 2 ^ (r.1.n - ((gate0 l F).budget kclk coef A a ha).kOf r.1.n / 4) * (r.1.n + 1) ^ Dq

end Sizes

section Choice

/-- N1's exponent. -/
noncomputable def dIn (h : ∀ l, FpInBound l) (l : Literals) (fe : ℕ) : ℕ := Classical.choose (h l fe)
/-- N1's coefficient. -/
noncomputable def kIn (h : ∀ l, FpInBound l) (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (h l F.filterErrDeg) F rfl)
theorem kIn_spec (h : ∀ l, FpInBound l) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    (fpIn l F kclk coef A a ha r).length + 1 ≤
      kIn h l F * 2 ^ (((gate0 l F).budget kclk coef A a ha).kOf r.1.n) * (r.1.n + 1) ^ dIn h l F.filterErrDeg :=
  Classical.choose_spec (Classical.choose_spec (h l F.filterErrDeg) F rfl) kclk coef A a ha r

/-- N2's exponent. -/
noncomputable def dE (h : ∀ l, SeedCountBound l) (l : Literals) (fe : ℕ) : ℕ := Classical.choose (h l fe)
/-- N2's coefficient. -/
noncomputable def kE (h : ∀ l, SeedCountBound l) (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (h l F.filterErrDeg) F rfl)
theorem kE_spec (h : ∀ l, SeedCountBound l) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    seedCount l F kclk coef A a ha r ≤ kE h l F * (r.1.n + 1) ^ dE h l F.filterErrDeg :=
  Classical.choose_spec (Classical.choose_spec (h l F.filterErrDeg) F rfl) kclk coef A a ha r

/-- N3's exponent. -/
noncomputable def dQ (h : ∀ l, PtCountBound l) (l : Literals) (fe : ℕ) : ℕ := Classical.choose (h l fe)
/-- N3's coefficient. -/
noncomputable def kP (h : ∀ l, PtCountBound l) (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (h l F.filterErrDeg) F rfl)
theorem kP_spec (h : ∀ l, PtCountBound l) (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) :
    ptCount l F kclk coef A a ha r ≤
      kP h l F * 2 ^ (r.1.n - ((gate0 l F).budget kclk coef A a ha).kOf r.1.n / 4) * (r.1.n + 1) ^ dQ h l F.filterErrDeg :=
  Classical.choose_spec (Classical.choose_spec (h l F.filterErrDeg) F rfl) kclk coef A a ha r

end Choice

/-! ## The bookkeeping -/

section Arith

end Arith

/-! ## S6 -/

section S6
variable (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha))

/-- **S6's `fits`** at `E₅ = e5 …` (before `F`), `CD₅ = 1`, `c₅ = c5v …` (after `F`). -/
theorem s6_fits (U : S6Uni Sw X bridgeT front o sc O) (h1 : ∀ l, FpInBound l) (h2 : ∀ l, SeedCountBound l)
    (h3 : ∀ l, PtCountBound l) :
    S6Fits Sw X bridgeT front o sc O (fun l fe => e5 (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe))
      (fun _ _ => 1)
      (fun l fe F => c5v (U.Cg l fe F) (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe) (kIn h1 l F) (kE h2 l F)
        (kP h3 l F)) := by
  intro l fe F hfe _ hCD kclk coef A a ha
  subst hfe
  unfold FitsRes
  intro r
  obtain ⟨dDf, dDw, dDt, dDp, dDo, dOD⟩ := U.hD l F kclk coef A a ha
  obtain ⟨cCf, cCw, cCt, cCp, cCo, cOC⟩ := U.hC l F kclk coef A a ha
  obtain ⟨-, -, -, -, -, hs, -⟩ := r.2
  obtain ⟨-, hr2, hr4, -⟩ := hs
  have hn : 1 ≤ r.1.n := by omega
  have hCD1 : 1 ≤ F.CD := hCD
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf r.1.n ≤ ((gate0 l F).budget kclk coef A a ha).psiOf r.1.n :=
    le_trans (Nat.le_add_right _ _) (FinalPass.SymFr.kL_le_loadPsi F.CD _ (Nat.clog 2 (r.1.n + 2)) _ _ hCD1)
  exact fits_arith hn hk (kIn_spec h1 l F kclk coef A a ha r) (Nat.le_add_left _ _) (kE_spec h2 l F kclk coef A a ha r)
    (kP_spec h3 l F kclk coef A a ha r) ((front l F kclk coef A a ha).W_le r) dDf dDw dDt dDp dDo dOD
    cCf cCw cCt cCp cCo cOC

/-- **S6's target** (`S6Uni → S6Out`) from the three request-size bounds. -/
noncomputable def s6Target (h1 : ∀ l, FpInBound l) (h2 : ∀ l, SeedCountBound l) (h3 : ∀ l, PtCountBound l) :
    S6Target Sw X bridgeT front o sc O := fun U =>
  ⟨fun l fe => e5 (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe), fun _ _ => 1,
    fun l fe F => c5v (U.Cg l fe F) (U.Dg l fe) (dIn h1 l fe) (dE h2 l fe) (dQ h3 l fe) (kIn h1 l F) (kE h2 l F)
      (kP h3 l F), s6_fits Sw X bridgeT front o sc O U h1 h2 h3⟩

end S6

end NearCubicWires.WireExponent3_5.PrimAsm.S6Fit

end
