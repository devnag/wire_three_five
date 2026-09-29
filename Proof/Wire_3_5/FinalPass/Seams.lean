import Proof.Wire_3_5.FinalPass.NumDen
import Proof.Wire_3_5.FinalPass.PlanFP

/-! # The final pass's seams: seeds → out, and the per-point value (P3:3170-3181)

The seeds phase (S4) leaves the printed value as two naturals in fixed-width binary (`NumDenOut`: `frame (binary W
numOf)` on `tN`, `frame (binary W denOf)` on `tD`, all heads at `0`), and the out machine (X6, `OutMachine`) prints
`ratWord (Num / Den)`: `OutMachine.phase` is `FpPhases.out` from any such exit (`fpOut_eq`, `NumDen.value_eq`).
The per-point evaluators (S2 THR, S3 SYM) add `ptThr` / `ptSym` at the point `(c, u_ℓ, v_ℓ)` and filter seed `e`:
`thrNum = Σ_c Σ_e Σ_ℓ ptThr` (`thrNum_pt`), `symNum = Σ_c Σ_e Σ_ℓ ptSym` (`symNum_pt`; `ptSym` sums over the list
seeds); `PtEval` is their common result shape (accumulator `+= val`, nothing else changed, polynomial bound). Main
declarations: `fpNum`, `fpDen`, `fpOut_eq`, **`NumDenOut`**, **`OutMachine`**, `OutMachine.phase`, `ptThr`, `ptSym`,
`thrNum_pt`, `symNum_pt`, **`PtEval`**. Paper quantities: the printed value `ratWord (greedyValue)` and its per-point
terms `M·R̂`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

/-! ## Seeds → out -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The numerator at a request of the family. -/
noncomputable abbrev fpNum (r : FReq l F kclk coef A a ha) : ℕ :=
  numOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

/-- The denominator (`≥ 1`) at a request of the family. -/
noncomputable abbrev fpDen (r : FReq l F kclk coef A a ha) : ℕ :=
  denOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

theorem fpOut_eq (r : FReq l F kclk coef A a ha) :
    fpOut l F kclk coef A a ha r = ratWord ((fpNum l F kclk coef A a ha r : ℚ) / fpDen l F kclk coef A a ha r) := by
  unfold fpOut; rw [value_eq]

/-- **The seeds phase's exit** (S4 → out): the numerator and the denominator framed in `W`-bit binary on `tN`, `tD`,
every head at `0`. -/
structure NumDenOut {t : ℕ} (tN tD : Fin t) (W : FReq l F kclk coef A a ha → ℕ)
    (H : FReq l F kclk coef A a ha → Fin t → ℕ) (Ab : FReq l F kclk coef A a ha → Fin t → List Bool) : Prop where
  ne : tN ≠ tD
  heads : ∀ r, H r = fun _ => 0
  num : ∀ r, Ab r tN = frame (binary (W r) (fpNum l F kclk coef A a ha r))
  den : ∀ r, Ab r tD = frame (binary (W r) (fpDen l F kclk coef A a ha r))
  numW : ∀ r, fpNum l F kclk coef A a ha r < 2 ^ W r
  denW : ∀ r, fpDen l F kclk coef A a ha r < 2 ^ W r

end Family

/-! ## The per-point value -/

section Point
variable (P : StarParams) (σ : P.Translation) {a : ℕ} {N Q : ℕ} (eqv : P.Errors ≃ Fin N)
  (S : Fin Q → Fin N × Fin N)

/-- **The THR per-point value** at center `c`, filter seed `e`, sample `ℓ`: `Σ_{g,p} M·R̂_{g,p}`. -/
def ptThr (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n)) (FP : GapParams)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)
    (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) : ℕ :=
  ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
    (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
      (thrRhat P Cs algorithm den report gp.1 gp.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)).toNat

theorem thrNum_pt (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) :
    thrNum P σ eqv S Cs carriers FP algorithm den report =
      ∑ c, ∑ e, ∑ l, ptThr P σ eqv S Cs carriers FP algorithm den report c e l := rfl

/-- **The SYM per-point value** at center `c`, filter seed `e`, sample `ℓ`: `Σ_{e'} M·R̂_{e'}` over the list seeds. -/
def ptSym (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n)) (FP : GapParams)
    (Pl : FlatListParams) (c : {c // P.IsCenter σ c}) (e : GapSeed FP) (l : Fin Q) : ℕ :=
  ∑ el : Pl.FlatSeed,
    (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
      (symRhatFast P Cs Pl el c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)).toNat

theorem symNum_pt (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) :
    symNum P σ eqv S Cs carriers FP Pl = ∑ c, ∑ e, ∑ l, ptSym P σ eqv S Cs carriers FP Pl c e l := by
  unfold symNum ptSym
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_comm]

end Point

end NearCubicWires.WireExponent3_5.FinalPass.Seams
