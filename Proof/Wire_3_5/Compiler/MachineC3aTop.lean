import Proof.Packets.PacketsGlueMetaMul
import Proof.SourceAssembly.SourceLiveCount
import Proof.SourceAssembly.SourceRequestCurComp
import Proof.Wire_3_5.Compiler.MachineC3aPO

/-! # C3a′'s machine: the layout, the stages, the capacities and the cost (P3:1596-1664, 1896-1906)

Paper: alg:disjoint ("Construction is polynomial in the explicit output size", P3:1604-1615) and alg:pullback in the
star instance (P3:1636-1664). C3a's machine runs on `Fin (81 + (Dec.DT a + 1))`: 81 tapes of its own (the input, the
loaded record and fields, the stage log, the unary counts and constants, the pool builder's tapes, the output), then
base's decomposition layout (`Dec`), whose ports are mapped onto the left part (`portsL`). Twenty-four stages, each
starting and ending with every head at cell `0`:
load (the C3 loader), the domain template, `1^{|seg|}` (length, then unary), the decomposition (`Dec.decM`), `1^B`,
`1^{|flips|}`, `1^{P_ex}` and `1^{#atoms}` (unary products), the side counts, the two padding counts (unary
subtraction), the counter, the zero registers, the cell, the entry registers and mask, the two zero-padding streams,
and the pool with its output word (`PO.poM`). The log tapes start blank at the capacities `c3aCapL` (base's
`ZeroPadding.run_unpad` then runs the machine from empty tapes). The paper quantity is the pool builder's construction:
its machine `c3aM` and its cost `c3aCost`. Main declarations: the slot maps, the parameters, `c3aCapL`, `c3aCap`,
`c3aM`, `c3aCost`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

variable (a : DecompositionAlgorithm)

/-! ## The layout -/

/-- The right part: the decomposition stage's tapes. -/
abbrev MR : ℕ := C3a.Dec.DT a + 1
/-- The whole layout. -/
abbrev U : ℕ := 81 + MR a
/-- A slot map on the left part. -/
def sh {k : ℕ} (sl : Fin k → Fin 81) : Fin k → Fin (U a) := shiftL (MR a) sl

def l0 : Fin (13 + 1) → Fin 81 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def l1 : Fin 3 → Fin 81 := ![2, 14, 15]
def l2 : Fin 2 → Fin 81 := ![3, 16]
def l3 : Fin 3 → Fin 81 := ![16, 17, 18]
def l5 : Fin 3 → Fin 81 := ![22, 24, 25]
def l6 : Fin (2 + 1) → Fin 81 := ![6, 26, 13]
def l7 : Fin 4 → Fin 81 := ![26, 22, 27, 28]
def l8 : Fin 4 → Fin 81 := ![26, 23, 29, 30]
def l9 : Fin (3 + 1) → Fin 81 := ![4, 31, 32, 13]
def l10 : Fin 9 → Fin 81 := ![5, 31, 33, 34, 35, 36, 37, 38, 39]
def l11 : Fin 9 → Fin 81 := ![5, 32, 40, 41, 42, 43, 44, 45, 46]
def l12 : Fin (3 + 1) → Fin 81 := ![7, 24, 47, 13]
def l13 : Fin (2 + 1) → Fin 81 := ![7, 48, 13]
def l14 : Fin (2 + 1) → Fin 81 := ![24, 49, 13]
def l15 : Fin (2 + 1) → Fin 81 := ![24, 50, 13]
def l16 : Fin (2 + 1) → Fin 81 := ![24, 51, 13]
def l17 : Fin 1 → Fin 81 := ![53]
def l18 : Fin (3 + 1) → Fin 81 := ![8, 27, 54, 13]
def l19 : Fin (3 + 1) → Fin 81 := ![8, 27, 56, 13]
def l20 : Fin (3 + 1) → Fin 81 := ![8, 27, 55, 13]
def l21 : Fin (4 + 1) → Fin 81 := ![7, 33, 57, 59, 13]
def l22 : Fin (4 + 1) → Fin 81 := ![7, 40, 58, 59, 13]
def l23 : Fin (40 + 1) → Fin 81 := ![21, 47, 60, 48, 61, 72, 2, 73, 24, 4, 62, 63, 64, 65, 66, 67, 68, 69, 74, 57, 58, 70, 75, 76, 6, 20, 49, 50, 51, 52, 53, 54, 55, 56, 71, 77, 78, 79, 80, 29, 13]

theorem l0_inj : Function.Injective l0 := by decide
theorem l1_inj : Function.Injective l1 := by decide
theorem l2_inj : Function.Injective l2 := by decide
theorem l3_inj : Function.Injective l3 := by decide
theorem l5_inj : Function.Injective l5 := by decide
theorem l6_inj : Function.Injective l6 := by decide
theorem l7_inj : Function.Injective l7 := by decide
theorem l8_inj : Function.Injective l8 := by decide
theorem l9_inj : Function.Injective l9 := by decide
theorem l10_inj : Function.Injective l10 := by decide
theorem l11_inj : Function.Injective l11 := by decide
theorem l12_inj : Function.Injective l12 := by decide
theorem l13_inj : Function.Injective l13 := by decide
theorem l14_inj : Function.Injective l14 := by decide
theorem l15_inj : Function.Injective l15 := by decide
theorem l16_inj : Function.Injective l16 := by decide
theorem l17_inj : Function.Injective l17 := by decide
theorem l18_inj : Function.Injective l18 := by decide
theorem l19_inj : Function.Injective l19 := by decide
theorem l20_inj : Function.Injective l20 := by decide
theorem l21_inj : Function.Injective l21 := by decide
theorem l22_inj : Function.Injective l22 := by decide
theorem l23_inj : Function.Injective l23 := by decide

/-- The decomposition stage's ports (its framed stream, source, domain, `1^P`, counts, body, total, driver, log). -/
def pD : Fin 9 → Fin (MR a) :=
  ![(C3a.Dec.iFS a).castAdd 1, (C3a.Dec.iC a (C3a.Dec.pStr a)).castAdd 1, (C3a.Dec.iC a (C3a.Dec.pDom a)).castAdd 1,
    (C3a.Dec.iC a (C3a.Dec.pP a)).castAdd 1, (C3a.Dec.iC a (C3a.Dec.pCnt a)).castAdd 1,
    (C3a.Dec.iC a (C3a.Dec.pBod a)).castAdd 1, (C3a.Dec.iC a (C3a.Dec.pTot a)).castAdd 1,
    (C3a.Dec.iC a (C3a.Dec.pDrv a)).castAdd 1, Fin.natAdd (C3a.Dec.DT a) (0 : Fin 1)]
/-- Their places on the left part. -/
def qD : Fin 9 → Fin 81 := ![3, 19, 14, 17, 20, 21, 22, 23, 13]

/-! ## The request's parameters -/

def segR (R : PoolReq) : List Bool := C3a.Dec.segOf R.n R.gates
def BR (R : PoolReq) : ℕ := B a R.gates
def FR (R : PoolReq) : ℕ := R.flips.length
def GR (R : PoolReq) : ℕ := R.gates.length
def PexR (R : PoolReq) : ℕ := FR R * BR a R
def nTR (R : PoolReq) : ℕ := (R.side.filter id).length
def nFR (R : PoolReq) : ℕ := (R.side.filter (fun b => !b)).length
def kLR (R : PoolReq) : ℕ := R.width - nTR R
def kRR (R : PoolReq) : ℕ := R.width - nFR R
def SR (R : PoolReq) : ℕ := R.width + 2
def CsR (R : PoolReq) : ℕ := 2 * R.width + 5
def capKR (R : PoolReq) : ℕ := R.h + BR a R + 1
def WcR (R : PoolReq) : ℕ := BR a R + 1

/-- The pool builder's first register log (every conversion and register width it records). -/
def capR (R : PoolReq) : ℕ :=
  (2 * R.h + 1) + (2 * R.n + 1) + (2 * (R.Q + FR R * (counts a R.gates).sum + 1) + 1) + (2 * WcR a R + 2) +
    (3 * WcR a R + 2) + ((GS a R.gates).flatMap fun e => (List.ofFn e.weight ++ [e.target]).map fun z => convCost z.natAbs).sum
def capN2R (R : PoolReq) : ℕ := innerCost R.h R.n
def capN7R (R : PoolReq) : ℕ := normCost R.h R.n (GS a R.gates).length
def capC2R (R : PoolReq) : ℕ := cloopCost R.h R.n
def capC3R (R : PoolReq) : ℕ :=
  appCost R.h (2 * nLeft R.side R.n) (2 * (R.width - nLeft R.side R.n)) (2 * nRight R.side R.n)
    (2 * (R.width - nRight R.side R.n))
def capC4R (R : PoolReq) : ℕ := kidsCost R.h R.n R.width (nLeft R.side R.n) (nRight R.side R.n) (GS a R.gates).length
def capF8R (R : PoolReq) : ℕ :=
  R.flips.length * (flipCost R.h R.n R.width (nLeft R.side R.n) (nRight R.side R.n) (GS a R.gates).length + 2) + 1
def cap5R (R : PoolReq) : ℕ := gatesCost R.Q (FR R * (counts a R.gates).sum) (WcR a R) (BR a R) (counts a R.gates).length
/-- The pool builder's cost. -/
def pcR (R : PoolReq) : ℕ :=
  poolCost R.h R.Q (WcR a R) (BR a R) R.n R.width (nLeft R.side R.n) (nRight R.side R.n) (GS a R.gates).length
    R.flips.length (FR R * (counts a R.gates).sum) (counts a R.gates).length
def capPR (R : PoolReq) : ℕ := pcR a R

/-- The pool stage's inner cost. -/
def poInR (R : PoolReq) : ℕ :=
  PO.poInnerCost (pcR a R) (FR R * GR R) (FR R * (counts a R.gates).sum) (R.Q + FR R * (counts a R.gates).sum + 1)

/-- The input record's fields. -/
def recR (R : PoolReq) : List Bool := C3a.c3aInput R

/-- The shared stage log: every masked stage's raw cost. -/
def capSR (R : PoolReq) : ℕ :=
  (2 * (recR R).length + 1) + Top.loadChainCost (List.replicate R.n true) (frame (segR R)) (frame R.side)
    (List.replicate R.width true) (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] [] +
  C3a.Dec.innerCost a R.n R.gates + C3a.Count.nfLoopCost (FR R) R.n + C3a.Count.scLoopCost R.side.length +
  C3a.Const.kRawCost R.h (BR a R) + Top.wRunCost R.h + Top.w2Cost [true, false] [true, false, false] (BR a R) +
  C3a.Const.entRawCost R.Q (PexR a R) + Top.w4Cost [true, false] [true, false] [true, true] [false] R.Q (PexR a R) +
  C3a.Const.zpRawCost R.h (kLR R) + C3a.Const.zpRawCost R.h (kRR R) + poInR a R

/-- The capacity table of the left part from the capacities of its roles (the stage log, the record writer's log,
the subtraction scratch and log, the pool builder's logs and mask log). -/
def capVec (capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ) : Fin 81 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, capS, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, S, S, S, S, S, S, Cs, S, S, S, S, S, S, Cs, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, capI, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cap, capN2, capC2, capC3, capC4, cap5, capN7, capF8, capP]

/-- **The log capacities** of the left part (the stage log, the subtraction scratch, the cells, the record log, the
pool builder's logs). -/
def c3aCapL (R : PoolReq) : Fin 81 → ℕ :=
  capVec (capSR a R) (C3a.Const.recRawCost R.h) (SR R) (CsR R) (capR a R) (capN2R R) (capN7R a R) (capC2R R)
    (capC3R R) (capC4R a R) (capF8R a R) (cap5R a R) (capPR a R)

/-- The capacities of the whole layout (the decomposition's tapes start empty). -/
def c3aCap (R : PoolReq) : Fin (U a) → ℕ := Fin.addCases (c3aCapL a R) (fun _ => 0)


/-! ## The stages -/

noncomputable def m0 := RecoveryFocus.machine (sh a l0) Top.loadM
noncomputable def m1 := RecoveryFocus.machine (sh a l1) (RepairSource.ProjectionNormalization.DimensionTemplate.machine false)
noncomputable def m2 := RecoveryFocus.machine (sh a l2) ClockNumericPrep.ellMachine
noncomputable def m3 := RecoveryFocus.machine (sh a l3) (UWalkUnary.machine false false)
noncomputable def m4 := RecoveryFocus.machine (portsL (pD a) qD) (C3a.Dec.decM a)
noncomputable def m5 := RecoveryFocus.machine (sh a l5) (UWalkUnary.machine false false)
noncomputable def m6 := RecoveryFocus.machine (sh a l6) C3a.Count.nfM
noncomputable def m7 := RecoveryFocus.machine (sh a l7) ClockUnaryProduct.machine
noncomputable def m8 := RecoveryFocus.machine (sh a l8) ClockUnaryProduct.machine
noncomputable def m9 := RecoveryFocus.machine (sh a l9) C3a.Count.scM
noncomputable def m10 := RecoveryFocus.machine (sh a l10) SourceRequest.CurComp.subLocal
noncomputable def m11 := RecoveryFocus.machine (sh a l11) SourceRequest.CurComp.subLocal
noncomputable def m12 := RecoveryFocus.machine (sh a l12) C3a.Const.kM
noncomputable def m13 := RecoveryFocus.machine (sh a l13) (Top.wRunM false)
noncomputable def m14 := RecoveryFocus.machine (sh a l14) (Top.w2RM [true, false] [true, false, false])
noncomputable def m15 := RecoveryFocus.machine (sh a l15) (Top.w2RM [true, false] [true, false, false])
noncomputable def m16 := RecoveryFocus.machine (sh a l16) (Top.w2RM [true, false] [true, false, false])
noncomputable def m17 := RecoveryFocus.machine (sh a l17) (Kit.cellM true)
noncomputable def m18 := RecoveryFocus.machine (sh a l18) C3a.Const.entM
noncomputable def m19 := RecoveryFocus.machine (sh a l19) C3a.Const.entM
noncomputable def m20 := RecoveryFocus.machine (sh a l20) (Top.w4RM [true, false] [true, false] [true, true] [false])
noncomputable def m21 := RecoveryFocus.machine (sh a l21) C3a.Const.zpM
noncomputable def m22 := RecoveryFocus.machine (sh a l22) C3a.Const.zpM
noncomputable def m23 := RecoveryFocus.machine (sh a l23) C3a.PO.poM

/-- **C3a′'s machine**: the twenty-four stages in sequence. -/
noncomputable def c3aM := Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (m0 a) (m1 a)) (m2 a)) (m3 a)) (m4 a)) (m5 a)) (m6 a)) (m7 a)) (m8 a)) (m9 a)) (m10 a)) (m11 a)) (m12 a)) (m13 a)) (m14 a)) (m15 a)) (m16 a)) (m17 a)) (m18 a)) (m19 a)) (m20 a)) (m21 a)) (m22 a)) (m23 a)

/-! ## The cost -/

def cst0 (R : PoolReq) : ℕ := Top.loadCost (List.replicate R.n true) (frame (segR R)) (frame R.side) (List.replicate R.width true)
    (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] []
def cst1 (R : PoolReq) : ℕ := 2 * R.n + 8
def cst2 (R : PoolReq) : ℕ := 4 * (segR R).length + 5
def cst3 (R : PoolReq) : ℕ := 2 * (segR R).length + 6
def cst4 (R : PoolReq) : ℕ := C3a.Dec.decCost a R.n R.gates
def cst5 (R : PoolReq) : ℕ := 2 * BR a R + 6
def cst6 (R : PoolReq) : ℕ := C3a.Count.nfCost (FR R) R.n
def cst7 (R : PoolReq) : ℕ := 2 * (FR R * (2 * BR a R + 3) + 2) + 2
def cst8 (R : PoolReq) : ℕ := 2 * (FR R * (2 * GR R + 3) + 2) + 2
def cst9 (R : PoolReq) : ℕ := C3a.Count.scCost R.side.length
def cst10 (R : PoolReq) : ℕ := SourceRequest.CurComp.subCost R.width
def cst11 (R : PoolReq) : ℕ := SourceRequest.CurComp.subCost R.width
def cst12 (R : PoolReq) : ℕ := C3a.Const.kCost R.h (BR a R)
def cst13 (R : PoolReq) : ℕ := 2 * Top.wRunCost R.h + 2
def cst14 (R : PoolReq) : ℕ := 2 * Top.w2Cost [true, false] [true, false, false] (BR a R) + 2
def cst15 (R : PoolReq) : ℕ := 2 * Top.w2Cost [true, false] [true, false, false] (BR a R) + 2
def cst16 (R : PoolReq) : ℕ := 2 * Top.w2Cost [true, false] [true, false, false] (BR a R) + 2
def cst17 (_R : PoolReq) : ℕ := 1
def cst18 (R : PoolReq) : ℕ := C3a.Const.entCost R.Q (PexR a R)
def cst19 (R : PoolReq) : ℕ := C3a.Const.entCost R.Q (PexR a R)
def cst20 (R : PoolReq) : ℕ := 2 * Top.w4Cost [true, false] [true, false] [true, true] [false] R.Q (PexR a R) + 2
def cst21 (R : PoolReq) : ℕ := C3a.Const.zpCost R.h (kLR R)
def cst22 (R : PoolReq) : ℕ := C3a.Const.zpCost R.h (kRR R)
def cst23 (R : PoolReq) : ℕ := PO.poCost (pcR a R) (FR R * GR R) (FR R * (counts a R.gates).sum) (R.Q + FR R * (counts a R.gates).sum + 1)

/-- **The machine's cost**: the stages' costs and the sequencing steps. -/
def c3aCost (R : PoolReq) : ℕ :=
  ((((((((((((((((((((((cst0 R + 1 + cst1 R) + 1 + cst2 R) + 1 + cst3 R) + 1 + cst4 a R) + 1 + cst5 a R) + 1 + cst6 R) + 1 + cst7 a R) + 1 + cst8 R) + 1 + cst9 R) + 1 + cst10 R) + 1 + cst11 R) + 1 + cst12 a R) + 1 + cst13 R) + 1 + cst14 a R) + 1 + cst15 a R) + 1 + cst16 a R) + 1 + cst17 R) + 1 + cst18 a R) + 1 + cst19 a R) + 1 + cst20 a R) + 1 + cst21 R) + 1 + cst22 R) + 1 + cst23 a R

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
