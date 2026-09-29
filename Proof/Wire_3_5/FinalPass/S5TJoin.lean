import Proof.Wire_3_5.FinalPass.S5TFoc

/-! # S5-THR, part 33: the THR call's hash parameters, the joins (P3:2150-2157, 2220-2231, 2596-2599)

The THR path computes the fixed hash's data at W6's numbers (`mpOf v = thrMP v.M v.A v.Bs v.den`); the front's words
name the call's majorant `thrMajorant … (thrCallDen) (thrCallE) (thrCallT) (thrCallJ)` (`thrCallOf`). They are equal
(`Joins.thrNumVals_MP`, `thrNumVals_A`, the capTOf join `capTL_eq_capOf`); the hash bits' type depends on them, so
they are transported along the equality (`castS`).

* `castS`, `ofFn_castS`, `level_castS` (the transport); `bs_eq`, `tt_eq`, `jj_eq`, **`mp_eq`** (the join).

Paper quantity of the main type: the fixed hash's parameters `M, A, B_*, t, J` of a THR call (P3:2220-2231). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Split
open NearCubicWires.SupplierPipeline

/-- The hash bits transported along an equality of majorant parameters. -/
def castS {MP₁ MP₂ : MajorantParams} (h : MP₁ = MP₂) (s : Fin (2 * MP₁.t * MP₁.ell0) → Bool) :
    Fin (2 * MP₂.t * MP₂.ell0) → Bool := fun i => s (Fin.cast (by rw [h]) i)

theorem ofFn_castS {MP₁ MP₂ : MajorantParams} (h : MP₁ = MP₂) (s : Fin (2 * MP₁.t * MP₁.ell0) → Bool) :
    List.ofFn (castS h s) = List.ofFn s := by subst h; rfl

theorem level_castS {MP₁ MP₂ : MajorantParams} (h : MP₁ = MP₂) (s : Fin (2 * MP₁.t * MP₁.ell0) → Bool) :
    ListEval.levelWord MP₂.M MP₂.J MP₂.W (ListEval.rowsOf (MajorantBits.dataBits MP₂ (castS h s)) MP₂.M) =
      ListEval.levelWord MP₁.M MP₁.J MP₁.W (ListEval.rowsOf (MajorantBits.dataBits MP₁ s) MP₁.M) := by
  subst h; rfl

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem filt_cap (n : ℕ) :
    ((PrimAsm.Plan.callInputs l F kclk coef A a ha).filterParams .thr n).cap = PrimT.TS4.capTL l F.cr n :=
  (capTL_eq_capOf l F kclk coef A a ha n).symm

theorem bs_eq {n : ℕ} {a' : ℕ} (carriers : List (Stars.Carrier n)) :
    Primitive.thrCallBs (B := (gate0 l F).budget kclk coef A a ha) carriers (n := n) (a := a') =
      a' * (4096 * ((carriers.length + 1) * (4096 * PrimT.TS4.capTL l F.cr n))) := by
  unfold Primitive.thrCallBs; rw [capTL_eq_capOf l F kclk coef A a ha n]

/-- **The THR call's majorant is W6's.** -/
theorem mp_eq {n : ℕ} (hs : (PrimAsm.Plan.callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) :
    Primitive.thrMajorant ((PrimAsm.Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      ((PrimAsm.Plan.callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
      (Primitive.thrCallDen (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs)
      (Primitive.thrCallE (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs carriers)
      (Primitive.thrCallT (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs carriers)
      (Primitive.thrCallJ (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs carriers) =
    mpOf (vOf l F.cr ((PrimAsm.Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
      (PrimAsm.Plan.callInputs l F kclk coef A a ha).D carriers) := by
  have hMP := PrimThrW.Joins.thrNumVals_MP ((PrimAsm.Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs
    carriers ((PrimAsm.Plan.callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (PrimAsm.Plan.callInputs l F kclk coef A a ha).D
    (Primitive.thrCallE (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs carriers)
  rw [filt_cap] at hMP
  have hA := PrimThrW.Joins.thrNumVals_A (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs
    carriers.length (PrimT.TS4.capTL l F.cr n)
  have hT : Primitive.thrCallT (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs carriers =
      (vOf l F.cr ((PrimAsm.Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
        (PrimAsm.Plan.callInputs l F kclk coef A a ha).D carriers).tt := by
    unfold Primitive.thrCallT; rw [bs_eq l F kclk coef A a ha carriers, ← hA]; rfl
  have hJ : Primitive.thrCallJ (gate0 l F).alg (PrimAsm.Plan.callInputs l F kclk coef A a ha) hs Cs carriers =
      (vOf l F.cr ((PrimAsm.Plan.callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg
        (PrimAsm.Plan.callInputs l F kclk coef A a ha).D carriers).J := by
    unfold Primitive.thrCallJ; rw [bs_eq l F kclk coef A a ha carriers, ← hA]; rfl
  rw [hT, hJ]
  exact hMP

end Call

end NearCubicWires.WireExponent3_5.FinalPass.S5T
