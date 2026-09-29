import Proof.Wire_3_5.Foundations.Contracts
import Proof.Wire_3_5.Stars.StarSelectionChoice

/-! # C1, coset selection: the machine contract at the references (P3:1324-1362)

Realizes the seed's C1 contract `Machine.c1` (the five-field unit of `star:selection`: "For each partition, compute the
exact weighted objective [...] Select a minimum objective", P3:1329-1360, in the selection class
`2^{n/2+O(k)}poly(n)`, P3:1335, 1359-1360) at the verified references of `star:selection`: the objective of a coset is
`starObjectiveRef` (the row counts over the `2^k` error rows, the population gates and the corner patterns, equal to the
paper's `E_x Σ_X p_X R_X(x)` by `objective_eq_ref`), and the selected coset is `selectCodes` (the first minimizer over the
`2^k` code lists). The request's gates are the seed's `S0Stub.IntGate`s and its populations are gate-index lists with
rational weights; `popsOf` reads them as `(p_X, Carrier)`.

Main declarations: `ParamsOk` (the star parameters' conditions, decidable), `starParamsOf`, `gateOf`, `popsOf`,
`selObjective`, `selArgmin`, **`c1inst`** (`Machine.c1` at these references) and **`c1inst_err`** (the error field
holds for the reference on every admissible request: the selected coset has `r` codes and minimizes the objective over
every well-formed coset). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.Cost

/-- The star parameters' conditions (P3:1188-1189): `r` even, `2 ≤ r`, `4r ≤ n`. -/
def ParamsOk (R : SelectionReq) : Prop := R.r % 2 = 0 ∧ 2 ≤ R.r ∧ 4 * R.r ≤ R.n

instance (R : SelectionReq) : Decidable (ParamsOk R) := by unfold ParamsOk; infer_instance

/-- The star parameters of an admissible request. -/
def starParamsOf (R : SelectionReq) (h : ParamsOk R) : StarParams :=
  ⟨R.n, R.r, Nat.even_iff.mpr h.1, h.2.1, h.2.2⟩

/-- A seed gate as a normalized threshold gate (the same weights and threshold). -/
def gateOf {n : ℕ} (g : IntGate n) : NormalizedThresholdGate n := ⟨g.weights, g.threshold⟩

/-- The populations `(p_X, X)`, each carrier the listed gates (repeated occurrences kept, P3:1361-1362). -/
def popsOf (R : SelectionReq) : List (ℚ × Carrier R.n) :=
  R.pops.map fun X => (X.2, X.1.map fun i => gateOf (R.gates.getD i ⟨fun _ => 0, 0⟩))

/-- The objective of a coset (its codes): `starObjectiveRef` at the translation of the codes. -/
def selObjective (R : SelectionReq) (c : Coset) : ℚ :=
  if h : ParamsOk R then
    (starParamsOf R h).starObjectiveRef ((starParamsOf R h).translationOfCodes c) (popsOf R)
  else 0

/-- The selected coset: `selectCodes`. -/
def selArgmin (R : SelectionReq) : Coset :=
  if h : ParamsOk R then (starParamsOf R h).selectCodes (popsOf R) else []

/-- **The C1 contract at the verified references.** -/
def c1inst (E : Envelope) (encodeCoset : Coset → List Bool) (inputWord : SelectionReq → List Bool)
    (psi : SelectionReq → ℕ) (coef : ℕ) : MachineContract E :=
  c1 E selObjective selArgmin encodeCoset inputWord psi coef

end NearCubicWires.WireExponent3_5.SelectionMachine
