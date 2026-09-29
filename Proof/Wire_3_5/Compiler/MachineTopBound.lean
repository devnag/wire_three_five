import Proof.Wire_3_5.Compiler.MachineTopWord

/-! # C3 v2 top level, T6 (part 3a): the machine's cost is a polynomial of degree 8 (P3:1887-1888, 1905-1906)

Paper: "Construction takes `(input description size + 𝒮)·poly(n)` deterministic bit operations" (P3:1905-1906), with
`𝒮 ≤ A·2^m·Q'(P_ex+1)^{Q'd}` (P3:1892). The machine's cost `c3Cost a R` (the five stages and the final reset) is bounded
by one polynomial in a single quantity `X` that dominates every parameter of the run: the input length, the parameters
`Q', P_ex, m, p, width, h, d`, the list maxima of the expression's encoding, and the counts `(P_ex+1)^d`,
`Q'(P_ex+1)^{Q'd}`, `2^m·A`, the number of stacked occurrences. The only non-polynomial term of the cost functions, the
`(P_ex+1)^d` masks per monomial (`atomsCost`'s `K^n`), is threaded as its own argument (`subsetCostN`, …), and the
counter loop's `2^m` is bounded separately. **`gB_le`**: `gB X ≤ 52802·X^8` for `X ≥ 1`; **`c3Cost_le_gB`**:
`c3Cost a R ≤ gB X` when every parameter is at most `X` (the list's lengths at most `8·X²`). The paper quantity is the
construction cost `(input description size + 𝒮)·poly(n)`. Main declarations: the threaded cost functions, `hdrB`,
`gB`, **`gB_le`**, `subsets_le`, `emit_le`, `init_le`, `load_eq`, `hdr_le`, **`c3Cost_le_gB`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary

def atomsCostN (n P K L N : ℕ) : ℕ := n * (Masks.atomCost P K N L + 2) + 1
def monoCostN (n P Q W N : ℕ) : ℕ :=
  (2 * (2 * (2 * (Q + W + 1) + 1) + 2 + 1 + 1) + 2) + 1 + atomsCostN n P (W + 1) (Q + W + 1) N
def monoInsCostN (d P Q W B N : ℕ) : ℕ := 1 + 1 + monoCostN d P Q W N + 1 + 1 + 1 + Cancel.insertAllCost B B (Q + W + 1)
def factorCostN (NF CB d P Q W B N : ℕ) : ℕ :=
  1 + 1 + ((1 + 2 + 1 + (NF * (monoInsCostN d P Q W B N + 2) + 1)) + (NF * (1 + 1 + (2 * CB + 1) + 2) + 1) + 2) + 1 + 1 +
    1 + 1 + 1
def termCostN (CBW m NF CB d P Q W B NG NU N : ℕ) : ℕ :=
  2 * (2 * (2 * CBW + 1) + 2) + (2 * (1 + 1 + (m * (factorCostN NF CB d P Q W B N + 2) + 1)) + 2) +
    Unions.unionsCost NG NU (Q + W + 1) + (2 * (NU * (2 * (Q + W + 1) + 1 + 1 + 1 + 2) + 1) + 2) + 40
def subsetCostN (Vn CBW m NF CB d P Q W B NG NU N : ℕ) : ℕ :=
  (2 * (Vn * (termCostN CBW m NF CB d P Q W B NG NU N + 2) + 1) + 2) + 1 + (2 * (2 * m + 1) + 2) + 1 + (2 * (2 * m + 2) + 2)
def hdrB (X : ℕ) : ℕ :=
  (2 * w2Cost [true, true] [] X + 2) + 1 + (2 * X + 1) + 1 + (16 * (X + X) ^ 2 + 72 * (X + X) + 12 * (X + X + 1) + 58) + 1 +
    (2 * X + 1) + 1 + (8 * X * X * ((2 * (X + X + X) + 1) + 1 + 1 + 2) + 1)
def gB (X : ℕ) : ℕ :=
  2 * ((6 * X + 27) + 1 + initCost X X X (X + X) X + 1 +
    (2 * (X * (subsetCostN X X X X X X X X X X X X X + 2) + 1 + 1 + 1) + 2) + 1 +
    (2 * (Emit.emitCost X X X X (X + X) X X X X + 1 + 1) + 2) + 1 + hdrB X) + 2

theorem pw (X i j : ℕ) (hX : 1 ≤ X) (h : i ≤ j) : X ^ i ≤ X ^ j := Nat.pow_le_pow_right hX h

theorem gB_le (X : ℕ) (hX : 1 ≤ X) : gB X ≤ 52802 * X ^ 8 := by
  have h0 := pw X 0 8 hX (by norm_num)
  have h1 := pw X 1 8 hX (by norm_num)
  have h2 := pw X 2 8 hX (by norm_num)
  have h3 := pw X 3 8 hX (by norm_num)
  have h4 := pw X 4 8 hX (by norm_num)
  have h5 := pw X 5 8 hX (by norm_num)
  have h6 := pw X 6 8 hX (by norm_num)
  have h7 := pw X 7 8 hX (by norm_num)
  simp only [pow_zero, pow_one] at h0 h1
  simp only [gB, hdrB, subsetCostN, termCostN, factorCostN, monoInsCostN, monoCostN, atomsCostN, Masks.atomCost, Masks.lookupCost, Masks.lookUnitCost, Masks.expandLoopCost, Masks.outerCost, Masks.innerCost, Cancel.copyLoopCost, Cancel.insertAllCost, Cancel.allCost, Cancel.symCost, Cancel.filterLoopCost, Unions.unionsCost, Unions.aCost, Unions.liftCost, Unions.pass1Cost, Unions.uBodyCost, Kit.appendCost, initCost, w3Cost, w4Cost, wLastCost, wRunCost, w2Cost, cellsCost, loopCost, putsCost, Emit.emitCost, Emit.groupCost, Emit.entryCost, Emit.labelCost, Emit.armBound, Emit.trueCost, Emit.falseCost, Emit.mergeAllCost, Emit.mergeCost, Emit.copyCost, Emit.skipCost, Emit.coefRawCost, Emit.thermoCost, Emit.thermoOneCost, Emit.shiftCost, Emit.cut0Cost, Emit.cut1Cost, Emit.fieldCost, Emit.padCost, Emit.normCost, Emit.coefEmitCost, ts4]
  ring_nf
  linarith


variable (a : DecompositionAlgorithm)

/-- The compiler stages' cost is the threaded cost at `N = (P_ex+1)^d`. -/
theorem subsetCost_eq_N (Vn CBW m NF CB d P Q W B NG NU : ℕ) :
    Poly.subsetCost Vn CBW m NF CB d P Q W B NG NU = subsetCostN Vn CBW m NF CB d P Q W B NG NU ((W + 1) ^ d) := rfl

theorem subsetCostN_mono (Vn CBW m NF CB d P Q W B NG NU N X : ℕ) (hVn : Vn ≤ X) (hCBW : CBW ≤ X) (hm : m ≤ X)
    (hNF : NF ≤ X) (hCB : CB ≤ X) (hd : d ≤ X) (hP : P ≤ X) (hQ : Q ≤ X) (hW : W ≤ X) (hB : B ≤ X) (hNG : NG ≤ X)
    (hNU : NU ≤ X) (hN : N ≤ X) :
    subsetCostN Vn CBW m NF CB d P Q W B NG NU N ≤ subsetCostN X X X X X X X X X X X X X := by
  simp only [subsetCostN, termCostN, factorCostN, monoInsCostN, monoCostN, atomsCostN, Masks.atomCost, Masks.lookupCost, Masks.lookUnitCost, Masks.expandLoopCost, Masks.outerCost, Masks.innerCost, Cancel.copyLoopCost, Cancel.insertAllCost, Cancel.allCost, Cancel.symCost, Cancel.filterLoopCost, Unions.unionsCost, Unions.aCost, Unions.liftCost, Unions.pass1Cost, Unions.uBodyCost, Kit.appendCost]
  gcongr

/-- **The compiler stages' cost** at the bounding quantity. -/
theorem subsets_le (R : C3Req) (X : ℕ) (hV : R.V.length ≤ X) (hCBW : sCBW R ≤ X) (hm : R.m ≤ X) (hNF : sNF R ≤ X)
    (hCB : sCB R ≤ X) (hd : R.d ≤ X) (hP : (shapeOf (R.D a)).length ≤ X) (hQ : R.P.Q ≤ X) (hW : (shapeOf (R.D a)).flatten.length ≤ X)
    (hB : sB a R ≤ X) (hNG : sNG a R ≤ X) (hNU : sNU a R ≤ X) (hN : ((shapeOf (R.D a)).flatten.length + 1) ^ R.d ≤ X)
    (h2m : 2 ^ R.m ≤ X) :
    subsetsCost a R ≤ X * (subsetCostN X X X X X X X X X X X X X + 2) + 1 := by
  unfold subsetsCost
  rw [subsetCost_eq_N]
  have := subsetCostN_mono _ _ _ _ _ _ _ _ _ _ _ _ _ X hV hCBW hm hNF hCB hd hP hQ hW hB hNG hNU hN
  gcongr

/-- **The emit loop's cost** at the bounding quantity. -/
theorem emit_le (R : C3Req) (X : ℕ) (hX : 1 ≤ X) (hNX : 2 ^ R.m * R.V.length ≤ X)
    (hE : R.P.Q * ((poolChildren a R.P.gates R.P.flips).length + 1) ^ (R.P.Q * R.d) ≤ X) (hp : R.p ≤ X) (hQ : R.P.Q ≤ X)
    (hPC : (poolChildren a R.P.gates R.P.flips).length ≤ X) (hh : R.P.h ≤ X) (hw : R.P.width ≤ X) (hL : R.P.h * R.P.Q * R.d ≤ X) :
    emitCostR a R ≤ Emit.emitCost X X X X (X + X) X X X X := by
  unfold emitCostR
  simp only [Emit.emitCost, Emit.groupCost, Emit.entryCost, Emit.labelCost, Emit.armBound, Emit.trueCost, Emit.falseCost, Emit.mergeAllCost, Emit.mergeCost, Emit.copyCost, Emit.skipCost, Emit.coefRawCost, Emit.thermoCost, Emit.thermoOneCost, Emit.shiftCost, Emit.cut0Cost, Emit.cut1Cost, Emit.fieldCost, Emit.padCost, Emit.normCost, Emit.coefEmitCost, Kit.appendCost]
  gcongr

/-- **The constant writers' cost** at the bounding quantity. -/
theorem init_le (Q0 W m p1 w X : ℕ) (hQ : Q0 ≤ X) (hW : W ≤ X) (hm : m ≤ X) (hp : p1 ≤ X + X) (hw : w ≤ X) :
    initCost Q0 W m p1 w ≤ initCost X X X (X + X) X := by
  simp only [initCost, w3Cost, w4Cost, wLastCost, wRunCost, w2Cost, cellsCost, loopCost, putsCost, ts4]
  gcongr

/-- **The load's cost** is linear in the input's length. -/
theorem load_eq (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    loadCost f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = 6 * (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length + 27 := by
  simp only [loadCost, loadChainCost, loadRec, List.length_append, frame_length]
  ring

theorem natBitLength_le' (v : ℕ) : natBitLength v ≤ v + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1

/-- **The request writer's cost** at the bounding quantity. -/
theorem hdr_le (rs : List (List Bool)) (L n : ℕ) (h1 h2 : List Bool) (X : ℕ) (hrs : rs.length ≤ 8 * X * X)
    (hL : L ≤ X + X + X) (hn : n ≤ X) (hh1 : h1.length ≤ X) (hh2 : h2.length ≤ X) :
    hdrCost rs L n h1 h2 ≤ hdrB X := by
  have hb : EquationHeaderAppend.budget (n + n) ≤ 16 * (X + X) ^ 2 + 72 * (X + X) + 12 * (X + X + 1) + 58 := by
    unfold EquationHeaderAppend.budget
    have := natBitLength_le' (n + n)
    gcongr
    omega
  have hw : w2Cost [true, true] [] n ≤ w2Cost [true, true] [] X := by
    simp only [w2Cost, loopCost, putsCost]
    gcongr
  unfold hdrCost hdrB
  gcongr

/-- **The machine's cost at the bounding quantity**: when every parameter of the run is at most `X`, the cost is at most
`gB X`. -/
theorem c3Cost_le_gB (R : C3Req) (X : ℕ) (hX : 1 ≤ X) (hI : (c3Input a R).length ≤ X)
    (hQ : R.P.Q ≤ X) (hW : (shapeOf (R.D a)).flatten.length ≤ X) (hm : R.m ≤ X) (hp : R.p ≤ X) (hw : R.P.width ≤ X) (hh : R.P.h ≤ X)
    (hd : R.d ≤ X) (hV : R.V.length ≤ X) (hCBW : sCBW R ≤ X) (hNF : sNF R ≤ X) (hCB : sCB R ≤ X)
    (hP : (shapeOf (R.D a)).length ≤ X) (hB : sB a R ≤ X) (hNG : sNG a R ≤ X) (hNU : sNU a R ≤ X)
    (hN : ((shapeOf (R.D a)).flatten.length + 1) ^ R.d ≤ X) (h2m : 2 ^ R.m ≤ X) (hNX : 2 ^ R.m * R.V.length ≤ X)
    (hE : R.P.Q * ((poolChildren a R.P.gates R.P.flips).length + 1) ^ (R.P.Q * R.d) ≤ X) (hPC : (poolChildren a R.P.gates R.P.flips).length ≤ X)
    (hL : R.P.h * R.P.Q * R.d ≤ X) (hn : (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length ≤ X) (hh1 : (natWord R.dRow ++ natWord (R.p + 1)).length ≤ X)
    (hh2 : (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols).length ≤ X) (hrs : (sfRecs a R).length ≤ 8 * X * X) :
    c3Cost a R ≤ gB X := by
  have e1 : loadCost (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)) = 6 * (c3Input a R).length + 27 := load_eq _ _ _ _ _ _ _ _ _ _ _
  have e2 := init_le (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width X (by omega) hW hm (by omega) hw
  have e3 := subsets_le a R X hV hCBW hm hNF hCB hd hP hQ hW hB hNG hNU hN h2m
  have e4 := emit_le a R X hX hNX hE hp hQ hPC hh hw hL
  have e5 := hdr_le (sfRecs a R) (R.p + 2) (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length (natWord R.dRow ++ natWord (R.p + 1)) (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols) X hrs (by omega) hn hh1 hh2
  unfold c3Cost topCost gB
  rw [e1]
  omega


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
