import Proof.Wire_3_5.FinalPass.SdSeed2

/-! # S4 (the seeds phase), part 19: one filter seed (P3:2036-2101, 3044-3048)

**`seedBody E`**: the seed flag down, `tTW` to the saved position, the seed's two tables moved into place, `tTW`
back (the position past the seed saved), the center loop at this seed, the next seed's test. `QHyp` bundles the seed
loop's hypotheses (the static facts `CStat` at the loop's entry state `ωQ`, the evaluator from any state agreeing with
`ωQ`, the mask capacities at every seed, the tables word within the capacity). `Gs e`: one seed's term, the sum over
the cell centers of the sampled pairs' terms (`sum_centers`, `ctrLoop_sum`). `sbCost`: one seed's step bound.
The run of one seed is part 20's `seedIter_spec`.

Paper quantity of the main type: one filter seed's term `Σ_c Σ_ℓ M(e, x_{c,ℓ})·Σ R̂(x_{c,ℓ})`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)
open NearCubicWires.SupplierWalk (majorityThreshold)

variable (E : SymPtEval2)

/-- **The seed loop's hypotheses** at its entry state `ωQ`. -/
structure QHyp (cap : ℕ) (FP : GapParams) (P : StarParams) (σT : P.Translation) (carriers : List (Stars.Carrier P.n))
    {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n) (Vf : BitInput P.n → Fin N → Fin N → ℕ)
    (s bb h tl T nE Vm : ℕ) (ωQ : BS E.nw E.nn E.nsc E.nrs) : Prop where
  R : CStat cap FP carriers P σT ps s bb h tl ωQ
  bs : bb + 1 = 2 ^ s
  n : h * bb + h * bb + tl = P.n
  kh : 1 ≤ s * h
  dl : ∀ a : Fin N, decWord bb h tl false (digitsOf s h (binary (s * h) a)) = List.ofFn (eu a)
  dr : ∀ b : Fin N, decWord bb h tl true (digitsOf s h (binary (s * h) b)) = List.ofFn (ev b)
  evq : ∀ ωR0 : BS E.nw E.nn E.nsc E.nrs, (∀ i, KeptC i → i ≠ tT 0 → i ≠ tT 1 → ωR0.st i = ωQ.st i) →
    ωR0.sh = ωQ.sh → (∀ q, q ≠ rgP → q ≠ fS → ωR0.val q = ωQ.val q) → ωR0.cell = ωQ.cell →
    ∀ (c : BitInput P.n) (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs), PtEnvC c (eu a) (ev b) ωR0 ω₀ →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ nE ∧ EvOut (Vf c a b) ω₀ ω₁
  Vle : ∀ c a b, Vf c a b ≤ Vm
  Vc : Vm ≤ cap
  capT : 2 * T + 2 < cap
  cs : 2 * 2 ^ s ≤ cap ∧ s ≤ cap ∧ 2 * P.n ≤ cap ∧ bb ≤ cap ∧ h ≤ cap ∧ tl ≤ cap
  p : ps.length * (2 * (2 * (s * h) + 1)) ≤ cap
  c8 : 8 * (P.n + 2) ≤ cap
  dT : dR P ≤ T ∧ dRow P ≤ T
  c2 : 2 * dR P + 1 ≤ cap ∧ 2 * dRow P + 1 ≤ cap
  mkc : ∀ (e : GapSeed FP) (k : Fin 2) (hk : k.val < carriers.length),
    MkCap cap (PrimT.tabH (carriers.get ⟨k.val, hk⟩)) P.n (maskGates (carriers.get ⟨k.val, hk⟩)).length
      (filterTable FP e (maskGates (carriers.get ⟨k.val, hk⟩)).length) (majorityThreshold FP.walkLen)
  regT : ωQ.val rgT = 0
  regB : ωQ.val rgB = 0
  twc : (ωQ.st tTW).length + 1 < cap

/-- One seed's term: the sum over the centers of the sampled pairs' terms. -/
def Gs (FP : GapParams) (e : GapSeed FP) (P : StarParams) (σT : P.Translation) (carriers : List (Stars.Carrier P.n))
    {N : ℕ} (ps : List (Fin N × Fin N)) (eu ev : Fin N → BitInput P.n) (Vf : BitInput P.n → Fin N → Fin N → ℕ) : ℕ :=
  ∑ c : {c // P.IsCenter σT c}, sSum FP e carriers c.1 eu ev (Vf c.1) ps

/-- **One filter seed.** -/
noncomputable def seedBody : BP E.nw E.nn E.nsc E.nrs :=
  .seq (.dec fS) (.seq fwdP (.seq (cpTB 0) (.seq (cpTB 1) (.seq rewP (.seq (ctrLoop E) peek)))))

/-- One seed's cost, at the tables word's length `Lw`. -/
def sbCost (FP : GapParams) (e : GapSeed FP) (P : StarParams) (carriers : List (Stars.Carrier P.n))
    (L s bb h tl nE Vm T Lw : ℕ) : ℕ :=
  1 + 1 + ((9 * Lw + 1) + 1 + (cpCost (tb FP e (Seams.carLen carriers 0)).length + 1 +
    (cpCost (tb FP e (Seams.carLen carriers 1)).length + 1 + ((9 * Lw + 1) + 1 +
      (clCost FP e P carriers L s bb h tl nE Vm T + 1 + (9 * Lw + 1 + 1 + (4 + 1 + (9 * Lw + 1))))))))

end NearCubicWires.WireExponent3_5.FinalPass.Sd
