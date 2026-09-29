import Proof.Wire_3_5.FinalPass.CoreIfaceM

/-! # The output machine: the carrier phase, types only

"For each name, use the regular filter of filt:gap on its signed mixed-residual population" (P3:3071-3076); a call
carries each named carrier `X` only as its code, and the final pass reads the carrier's atoms and their negations as
the table `gatesW h (maskGates X)` (P3:3049-3050, 3074-3080). The carrier phase is the pool writers' shared piece:
from the final pass's input `frame (fpIn r)` it runs `carTableM` per named carrier (the DataSetup carrier
blocks, `DataTabs.carT`) and leaves

* the two mask tables `carTab carriers k` (`k = 0, 1`; SA's slots 2–3),
* the two gate counts `1^{|X_k|}` (`0` past the carriers; SB's `carLen = 2·|X_k|`, `carLen_eq`),
* the carrier count `1^{|carriers|}` (SB),

with the input kept, every other stream `0^ℓ` (the table machine's scratch erased), every head and register `0`, at
both modes, within `Cs F·(|fpIn|+1)^{Ds fe}` steps: exactly the machine-level writer contract
`Finish.CoreWordsM l 5 (carWords l)`, so it docks into SA's and SB's writers like any `CoreWordsM` part.

* **`carCnt`**, **`carWords`** (the five words), **`carLen_eq`**;
* **`CarPhaseM l`** `:= Finish.CoreWordsM l 5 (carWords l)` (the deliverable, one machine per gate).

Paper quantity of the main type: the carriers' mask tables and gate counts (P3:3049-3050, 3071-3086). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams

/-- Carrier `k`'s gate count `|X_k|` (`0` past the carriers). -/
def carCnt {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) : ℕ :=
  if h : k < carriers.length then (carriers.get ⟨k, h⟩).length else 0

/-- The mask table's gate count is twice the carrier's. -/
theorem carLen_eq {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) : carLen carriers k = 2 * carCnt carriers k := by
  unfold carLen carCnt
  split_ifs with h
  · unfold Corner.maskGates
    simp only [List.length_flatMap, List.length_cons, List.length_nil]
    induction (carriers.get ⟨k, h⟩) with
    | nil => rfl
    | cons g X ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  · rfl

/-- **The carrier phase's five words** at a request: the mask tables of carriers `0`, `1` (SA's slots 2–3), their
gate counts in unary, the carrier count in unary. -/
noncomputable def carWords (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) : Fin 5 → List Bool :=
  ![carTab r.1.carriers 0, carTab r.1.carriers 1, List.replicate (carCnt r.1.carriers 0) true,
    List.replicate (carCnt r.1.carriers 1) true, List.replicate r.1.carriers.length true]

/-- **The carrier phase**: one machine per gate from `frame (fpIn r)` to the five carrier words, input kept,
residues `0^ℓ`, heads and registers `0`, at the machine-level writer contract. -/
abbrev CarPhaseM (l : Literals) : Type := Finish.CoreWordsM l 5 (carWords l)

end NearCubicWires.WireExponent3_5.FinalPass.Out.Car
