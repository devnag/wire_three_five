import Proof.Wire_3_5.Compiler.MachineC3aWord
import Proof.Wire_3_5.Compiler.MachineTopBound

/-! # C3a′'s machine: the cost of the stages other than the decomposition is one polynomial (P3:1614, 1661-1664)

Paper: "Construction is polynomial in the explicit output size" (alg:disjoint, P3:1614), and the pool's size
`P_ex ≤ 2^k n^{O(1)}` (P3:1661-1664), within the preprocessing class `2^{O(Ψ)}` (prim:runtime, P3:3105-3115). Every
stage of C3a's machine except the decomposition (whose cost is base's, `Dec.decCost`) has a cost that is a polynomial
with natural coefficients in the request's parameters. With one quantity `Y` dominating every parameter (the input's
length, `n`, `h`, `Q'`, the width, the gate count, the capacity `C` of the decomposition and the child count `B ≤ C`,
the flip count and `P_ex = |flips|·B`), the cost is at most `gA Y` plus the decomposition's cost
(**`c3aCost_le_gA`**), and **`gA_le`**: `gA Y D ≤ 10246·Y^4 + D` for `Y ≥ 1`. The only subtraction inside the pool builder's
cost (`childPassCost`'s `width − k`) is threaded by hand (`childT`). The paper quantity is the construction cost.
Main declarations: `childT`, `poolT`, `gA`, **`childPass_le`**, **`pool_le`**, **`gA_le`**, **`c3aCost_le_gA`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Bound
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
open NearCubicWires.RepairOrdinary

/-- `childPassCost` with every argument at `Y` (its differences `width − k` at most `Y`). -/
def childT (Y : ℕ) : ℕ := regCost Y + 1 + (regCost Y + 1 + ((2 * cloopCost Y Y + 2) + 1 +
  (tgtCost Y + 1 + ((2 * appCost Y (2 * Y) (2 * Y) (2 * Y) (2 * Y) + 2) + 1 + (regCost Y + 1 + regCost Y)))))

/-- `poolCost` with every argument at `Y`. -/
def poolT (Y : ℕ) : ℕ :=
  (2 * normCost Y Y Y + 2) + 1 + ((2 * (Y * ((2 * (2 * Y + 1) + 2 + 1 + (1 + 1 + (2 * (Y * (childT Y + 2) + 1) + 2)))
    + 2) + 1) + 2) + 1 + (1 + 1 + (Y * (tflipCost Y Y Y (Y + 1) Y Y + 2) + 1)))

/-- **The stages other than the decomposition, threaded at `Y`** (the decomposition's cost is `D`). -/
def gA (Y D : ℕ) : ℕ :=
  (6 * Y + 27) + 1 + (2 * Y + 8) + 1 + (4 * Y + 5) + 1 + (2 * Y + 6) + 1 + D + 1 + (2 * Y + 6) + 1 +
    C3a.Count.nfCost Y Y + 1 + (2 * (Y * (2 * Y + 3) + 2) + 2) + 1 + (2 * (Y * (2 * Y + 3) + 2) + 2) + 1 +
    C3a.Count.scCost Y + 1 + SourceRequest.CurComp.subCost Y + 1 + SourceRequest.CurComp.subCost Y + 1 +
    C3a.Const.kCost Y Y + 1 + (2 * Top.wRunCost Y + 2) + 1 + (2 * Top.w2Cost [true, false] [true, false, false] Y + 2) + 1 +
    (2 * Top.w2Cost [true, false] [true, false, false] Y + 2) + 1 +
    (2 * Top.w2Cost [true, false] [true, false, false] Y + 2) + 1 + 1 + 1 + C3a.Const.entCost Y Y + 1 +
    C3a.Const.entCost Y Y + 1 + (2 * Top.w4Cost [true, false] [true, false] [true, true] [false] Y Y + 2) + 1 +
    C3a.Const.zpCost Y Y + 1 + C3a.Const.zpCost Y Y + 1 + C3a.PO.poCost (poolT Y) Y Y (Y + Y + 1)

theorem pw4 (Y i : ℕ) (hY : 1 ≤ Y) (h : i ≤ 4) : Y ^ i ≤ Y ^ 4 := Nat.pow_le_pow_right hY h

/-- **The threaded cost is a polynomial of degree 4.** -/
theorem gA_le (Y D : ℕ) (hY : 1 ≤ Y) : gA Y D ≤ 10246 * Y ^ 4 + D := by
  have h0 := pw4 Y 0 hY (by norm_num)
  have h1 := pw4 Y 1 hY (by norm_num)
  have h2 := pw4 Y 2 hY (by norm_num)
  have h3 := pw4 Y 3 hY (by norm_num)
  simp only [pow_zero, pow_one] at h0 h1
  simp only [gA, poolT, childT, C3a.Count.nfCost, C3a.Count.nfLoopCost, C3a.Count.nfBodyCost, C3a.Count.scCost,
    C3a.Count.scLoopCost, SourceRequest.CurComp.subCost, C3a.Const.kCost, C3a.Const.kRawCost, Top.wRunCost,
    Top.w2Cost, Top.w4Cost, C3a.Const.entCost, C3a.Const.entRawCost, C3a.Const.zpCost, C3a.Const.zpRawCost,
    C3a.Const.zpBodyCost, C3a.Const.recRawCost, C3a.PO.poCost, C3a.PO.poInnerCost, C3a.Out.tabLoopCost,
    C3a.Out.atomCost, C3a.Out.cfCost, normCost, childCost, innerCost, fieldCostH, emitPairCost, regCost, cloopCost,
    coordCost, emitCost, addCost, tgtCost, appCost, appLoopCost, tflipCost, gatesCost, Pool.atomCost, labCost,
    Top.loopCost, Top.putsCost]
  ring_nf
  linarith

/-- **`childPassCost` below its threaded form** (the differences `width − k` at most `Y`). -/
theorem childPass_le (h n width kl kr Y : ℕ) (hh : h ≤ Y) (hn : n ≤ Y) (hw : width ≤ Y) (hkl : kl ≤ Y)
    (hkr : kr ≤ Y) : childPassCost h n width kl kr ≤ childT Y := by
  simp only [childPassCost, childT, appCost, appLoopCost, cloopCost, coordCost, emitCost, addCost, regCost, tgtCost]
  gcongr <;> omega

/-- **The pool builder's cost below its threaded form.** -/
theorem pool_le (h Q Wc V n width nL nR G F W c Y : ℕ) (hh : h ≤ Y) (hQ : Q ≤ Y) (hWc : Wc ≤ Y + 1) (hV : V ≤ Y)
    (hn : n ≤ Y) (hw : width ≤ Y) (hL : nL ≤ Y) (hR : nR ≤ Y) (hG : G ≤ Y) (hF : F ≤ Y) (hW : W ≤ Y) (hc : c ≤ Y) :
    poolCost h Q Wc V n width nL nR G F W c ≤ poolT Y := by
  have hcp := childPass_le h n width nL nR Y hh hn hw hL hR
  simp only [poolCost, poolT, flipCost, kidsCost, normCost, childCost, innerCost, fieldCostH, emitPairCost,
    tflipCost, gatesCost, Pool.atomCost, labCost]
  gcongr

variable (a : DecompositionAlgorithm)

/-- **The machine's cost below the threaded polynomial** (plus the decomposition's cost), when every parameter is at
most `Y`. -/
theorem c3aCost_le_gA (R : PoolReq) (Y : ℕ) (hI : (C3a.c3aInput R).length ≤ Y) (hn : R.n ≤ Y)
    (hseg : (segR R).length ≤ Y) (hB : BR a R ≤ Y) (hF : FR R ≤ Y) (hside : R.side.length ≤ Y) (hw : R.width ≤ Y)
    (hh : R.h ≤ Y) (hQ : R.Q ≤ Y) (hG : GR R ≤ Y) (hPex : PexR a R ≤ Y) (hkL : kLR R ≤ Y) (hkR : kRR R ≤ Y)
    (hFG : FR R * GR R ≤ Y) (hFc : FR R * (counts a R.gates).sum ≤ Y) (hpc : pcR a R ≤ poolT Y) :
    c3aCost a R ≤ gA Y (cst4 a R) := by
  have hI' : (Top.loadRec (List.replicate R.n true) (frame (segR R)) (frame R.side) (List.replicate R.width true)
      (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] []).length ≤ Y := hI
  unfold c3aCost cst0 cst1 cst2 cst3 cst5 cst6 cst7 cst8 cst9 cst10 cst11 cst12 cst13 cst14 cst15 cst16 cst17 cst18
    cst19 cst20 cst21 cst22 cst23 gA
  rw [Top.load_eq]
  simp only [C3a.Count.nfCost, C3a.Count.nfLoopCost, C3a.Count.nfBodyCost, C3a.Count.scCost,
    C3a.Count.scLoopCost, SourceRequest.CurComp.subCost, C3a.Const.kCost, C3a.Const.kRawCost, Top.wRunCost,
    Top.w2Cost, Top.w4Cost, C3a.Const.entCost, C3a.Const.entRawCost, C3a.Const.zpCost, C3a.Const.zpRawCost,
    C3a.Const.zpBodyCost, C3a.Const.recRawCost, C3a.PO.poCost, C3a.PO.poInnerCost, C3a.Out.tabLoopCost,
    C3a.Out.atomCost, C3a.Out.cfCost, Top.loopCost, Top.putsCost]
  gcongr

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Bound
