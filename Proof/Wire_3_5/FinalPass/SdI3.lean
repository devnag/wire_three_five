import Lean
import Proof.Wire_3_5.FinalPass.SdI2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdI3Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 (the seeds phase), part 52: the call's sizes below one polynomial `X = KX·(n+2)^{ZX}` (P3:3170-3178)

At a star call of the family every size the seeds phase's hypotheses name is at most `Xf n = KX·(n+2)^{ZX}`
(`AtomsX`, **`atoms_of`**: `n + 2`, the filter's `len, cap, errExp + 1`, the seeds `|E|`, the mask lengths, the
tables' widths `Hof`, the filter tables; `x_vsym`, `x_vthr`: the per-point values; `x_T`: the width `Tf`;
`x_ssz`/`x_sfn`, `x_tsz`/`x_tfn`: the evaluators' sizes and their `need`, `bound`), with `KX`, `ZX` from the literals,
the gate, the SYM evaluator's constants and the two size polynomials only (`SymSizeOK`, `ThrSizeOK`, the named
producers #124 and `ThrSz.thrSize_poly`).

Paper quantity of the main type: the call's sizes, polynomial in `n` (P3:3170-3178, "All powers of `n` are fixed
before a fixed `r`", P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
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
  52 + PrimAsm.CallIndex.gapZ l F + PrimAsm.CallIndex.capZ l F + ZV l F + Dsz * (E.D + 1) +
    Dtz * (ThrPt.thrPtProg.D + 1) + ZT l F

/-- The polynomial `X`'s coefficient. -/
noncomputable def KX (E : SymPtEval2) (Csz Ctz : ℕ) : ℕ :=
  1000 + 771 * (F.filterErrDeg + 1) + Csz + Ctz + (E.C + 1) * (Csz + 1) ^ E.D +
    (ThrPt.thrPtProg.C + 1) * (Ctz + 1) ^ ThrPt.thrPtProg.D + KT l F

variable (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM size hypothesis** (#124's statement at the family): polynomial in `n`. -/
def SymSizeOK (E : SymPtEval2) (Csz Dsz : ℕ) : Prop :=
  ∀ (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)),
    carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
    symSize E (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) ≤ Csz * (n + 1) ^ Dsz

/-- **The THR size hypothesis** (`ThrSz.thrSize_poly`'s statement at the family). -/
def ThrSizeOK (Ctz Dtz : ℕ) : Prop :=
  ∀ (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
    ThrPt.thrSize (thrCallOf (callInputs l F kclk coef A a ha) (gate0 l F).alg hs ha' Cs carriers translation) ≤
      Ctz * (n + 1) ^ Dtz

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

end
