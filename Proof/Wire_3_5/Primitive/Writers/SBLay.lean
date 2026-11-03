import Lean
import Proof.Wire_3_5.Primitive.Writers.SBP1R
import Proof.Wire_3_5.Primitive.Writers.SBCarBase
import Proof.Wire_3_5.Primitive.Writers.Dock0
import Proof.Wire_3_5.Primitive.Writers.SBInv
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Primitive.Writers.SymFam
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Primitive.Writers.SBLayBase


noncomputable section
set_option maxRecDepth 4096


/-! # SB, part (3a): SB's layout, machine and capacity split

* the layout: X6's streams (`fsX`) and registers (`frX`) first, the field phase's `23` streams `FsB`, the
  output streams `o6`, `o7`; the field registers `RbB = 96 …`; `sInB`, the count streams, `sOutB`;
* **`sbMach`**: X6's carrier pipeline docked (`wslot fsX frX`), then P1, the field phase, and the register clears;
* **`need_parts`**: every capacity hypothesis of the parts from `sbNeed ≤ cap`.

Paper quantities of the main types: S4's words `4 … 7` at a star call (`s4Core2`, P3:3170-3181) and SB's budget
(`prim:runtime`, P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarS
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums NearCubicWires.WireExponent3_5.PrimAsm.SBTypes
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-! ## Layout -/

/-! ## The machine -/

/-- **SB's machine at a gate**: X6's carrier pipeline (counts only) docked, P1, the field phase, the register clears. -/
noncomputable def sbMach (l : Literals) (F : GateFree l) : (s : ℕ) × Machine (nsB + 2 + NRB) s :=
  ⟨_, Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (wslot fsX frX) (carM DtC (eraseOf keepLS)))
    (p1W sInB cS0 cS1 cS6 o6 o7 F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)).toProg.compile)
    (SBField.fieldM FsB RbB)) (SBInv.clearAllW (List.finRange NRB)).toProg.compile⟩

/-! ## The capacity split -/

/-- **Every capacity hypothesis of SB's parts** from `sbNeed ≤ cap`. -/
theorem need_parts (l : Literals) (cr fe : ℕ) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ)
    (h : sbNeed l cr fe P m wl c0 c1 nc ≤ cap) :
    tB1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tB2a P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tB2b P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tB2c P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tC1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tC2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    tC3 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 ≤ cap ∧
    (P.n + 1) ^ 26 ≤ cap ∧ (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap ∧
    SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq P.n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n - 1) ≤ cap ∧
    2 ^ 40 * (CallIndexR.capK cr * (P.n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) m ≤ cap ∧
    Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n ≤ cap ∧
    2 * wl ≤ cap ∧ 2 ^ (natBitLength P.n + 1) ≤ cap ∧ c0 + 1 ≤ cap ∧ c1 + 1 ≤ cap ∧ nc + 1 ≤ cap ∧
    fe * Nat.clog 2 (P.n + 2) / 4 + 2 ≤ cap ∧
    (Data.unaryList (sbList P (Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2
      (gateCδ1 l) P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length ≤ cap ∧
    4 * ellOf P.n + 6 ≤ cap ∧ 2 ^ DtC * (wl + 1) ^ DtC ≤ cap := by
  unfold sbNeed at h
  generalize 2 ^ (natBitLength P.n + 1) = X at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- `CapNeed` at either mode from `capNeed_of`'s bound. -/
theorem capNeed_mode (l : Literals) (cr : ℕ) (m : Mode) (n cap : ℕ)
    (h : 2 ^ 40 * (CallIndexR.capK cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) m ≤ cap) :
    SymDec.CapNeed (gateCap l) m n (Ledger.rowBr cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) cap := by
  cases m
  · exact PrimT.TS4.capNeed_ofT l cr n cap h
  · exact SymFam.capNeed_of l cr n cap h

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
