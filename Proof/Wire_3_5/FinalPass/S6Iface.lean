import Proof.Wire_3_5.FinalPass.AssemblyDock3

/-! # S6's interface: the final pass's budget constants and `fits` from uniform phase constants

`finalPass_of3` (AssemblyDock3) takes the final pass's constants `E₅`, `CD₅`, `c₅` and the cost residual `fits`
(P3:3105-3115, 3170-3181: the phases' running time within `c₅·finalClasses E₅ (n, kOf n, psiOf n)`, the load
constant and the envelope fixed before the gate). S6 produces them from the three phases' explicit bounds:

* **`S6Fits`**: exactly `finalPass_of3`'s `fits` binder at given `E₅`, `CD₅`, `c₅`;
* **`S6Out`**: the constants with their `fits` (S6's deliverable);
* **`S6Uni`**: the uniformity bundle S6 may assume: every phase exponent (the front's `Df` and `Dw`, the seeds
  phase's `Dt`, `Dp`, `Do`, the out machine's `D`) at most `Dg l fe` (chosen before `F`), every coefficient (`Cf`,
  `Cw`, `Ct`, `Cp`, `Co`, `C`) at most `Cg l fe F` (the front's `W` is bounded by its own field `W_le` at `Cw`, `Dw`);
* **`S6Target`** (`S6Uni → S6Out`, the deliverable) and **`finalPass_of_s6`** (the dock: `finalPass_of3` at an
  `S6Out`).

Paper quantity of the main types: `c₅`, `E₅` and the final pass's cost residual (prim:runtime, P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams

/-- **`finalPass_of3`'s `fits`** at given constants `E₅`, `CD₅`, `c₅`. -/
def S6Fits (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha))
    (E₅ : (l : Literals) → ℕ → Envelope) (CD₅ : (l : Literals) → ℕ → ℕ)
    (c₅ : (l : Literals) → (fe : ℕ) → GateFree l → ℕ) : Prop :=
  ∀ (l : Literals) (fe : ℕ) (F : GateFree l), F.filterErrDeg = fe → ClassLE (E₅ l fe) F.E →
    CD₅ l fe ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FitsRes l F (E₅ l fe) (c₅ l fe F) kclk coef A a ha
        (s5Bound l F kclk coef A a ha (front l F kclk coef A a ha).Cf (front l F kclk coef A a ha).Df)
        (fun r => seedsShape (seedCount l F kclk coef A a ha r)
          (s5Bound l F kclk coef A a ha (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Ct (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dt r)
          (ptCount l F kclk coef A a ha r)
          ((bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Cp * (r.1.n + 1) ^ (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dp)
          (s5Bound l F kclk coef A a ha (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Co (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Do r))
        (fun r => (O l F kclk coef A a ha).C * ((front l F kclk coef A a ha).W r + 1) ^ (O l F kclk coef A a ha).D)

/-- **S6's deliverable**: the final pass's constants and their cost residual. -/
structure S6Out (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha)) where
  E₅ : (l : Literals) → ℕ → Envelope
  CD₅ : (l : Literals) → ℕ → ℕ
  c₅ : (l : Literals) → (fe : ℕ) → GateFree l → ℕ
  fits : S6Fits Sw X bridgeT front o sc O E₅ CD₅ c₅

/-- **The uniformity S6 may assume**: exponents at most `Dg l fe` (before `F`), coefficients at most `Cg l fe F`. -/
structure S6Uni (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha)) where
  Dg : Literals → ℕ → ℕ
  Cg : (l : Literals) → ℕ → GateFree l → ℕ
  hD : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    (front l F kclk coef A a ha).Df ≤ Dg l F.filterErrDeg ∧ (front l F kclk coef A a ha).Dw ≤ Dg l F.filterErrDeg ∧
    (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dt ≤ Dg l F.filterErrDeg ∧
    (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Dp ≤ Dg l F.filterErrDeg ∧
    (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Do ≤ Dg l F.filterErrDeg ∧
    (O l F kclk coef A a ha).D ≤ Dg l F.filterErrDeg
  hC : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    (front l F kclk coef A a ha).Cf ≤ Cg l F.filterErrDeg F ∧ (front l F kclk coef A a ha).Cw ≤ Cg l F.filterErrDeg F ∧
    (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Ct ≤ Cg l F.filterErrDeg F ∧
    (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Cp ≤ Cg l F.filterErrDeg F ∧
    (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).Co ≤ Cg l F.filterErrDeg F ∧
    (O l F kclk coef A a ha).C ≤ Cg l F.filterErrDeg F

/-- **S6's target**: the constants and `fits` from the uniformity bundle. -/
abbrev S6Target (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha)) : Type :=
  S6Uni Sw X bridgeT front o sc O → S6Out Sw X bridgeT front o sc O

/-- **The dock**: `finalPass_of3` at S6's deliverable. -/
noncomputable def finalPass_of_s6 (Sw : SymWords)
    (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SeedsWS2 l F kclk coef A a ha Sw)
    (bridgeT : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      SeedsWS2 l F kclk coef A a ha Sw → SeedsProg4 l F kclk coef A a ha Sw)
    (front : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      FrontPh3 l F kclk coef A a ha Sw (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)))
    (o : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t)
    (ho : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), (o l F kclk coef A a ha).val ≠ 0)
    (sc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), Fin (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t → Bool)
    (hoI : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).idle (o l F kclk coef A a ha) = true)
    (hsc : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), ∀ j, sc l F kclk coef A a ha j = true → (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).idle j = true)
    (O : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
      OutMachine2 (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).t (o l F kclk coef A a ha) (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tN (bridgeT l F kclk coef A a ha (X l F kclk coef A a ha)).tD (sc l F kclk coef A a ha))
    (S : S6Out Sw X bridgeT front o sc O) : (l : Literals) → FinalPassLeaf l :=
  finalPass_of3 Sw X bridgeT front o ho sc hoI hsc O S.E₅ S.CD₅ S.c₅ S.fits

end NearCubicWires.WireExponent3_5.FinalPass.Assembly
