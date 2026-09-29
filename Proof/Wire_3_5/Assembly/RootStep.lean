import Batteries.Tactic.OpenPrivate
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Std.Tactic
import Proof.Assembly.Budget
import Proof.Assembly.CappedEntryRuntime
import Proof.Assembly.FamilyFixedPhysicalRealization
import Proof.Assembly.FamilyRecord
import Proof.Assembly.RowsEntryCompatible
import Proof.Assembly.SelectedInputs
import Proof.Assembly.ValuesSym
import Proof.Assembly.ValuesThr
import Proof.CaseAnalysis.FinalCursorPrologueJoin
import Proof.MachineModel.ClosureActualReusableRow
import Proof.Packets.PacketsCombineTabRow
import Proof.Packets.PacketsCoordDock
import Proof.Packets.PacketsDriverPhase
import Proof.Packets.PacketsSeedDecode
import Proof.Packets.PacketsWinSum
import Proof.Rows.RowsFrameEntry
import Proof.Rows.RowsI2cPool
import Proof.Rows.RowsInitAssemblyRun
import Proof.Rows.ThresholdBit
import Proof.SourceAssembly.SourceSkelFinalAssembly
import Proof.SourceAssembly.SourceStepsIndexFit
import Proof.SourceAssembly.SourceStepsSeam
import Proof.Wire_3_5.Assembly.RootTop3
import Proof.Wire_3_5.Compiler.MachineEmitTwins
import Proof.Wire_3_5.Compiler.MachineTopClass
import Proof.Wire_3_5.FinalPass.CornerEval
import Proof.Wire_3_5.FinalPass.FiltTabBlock
import Proof.Wire_3_5.FinalPass.FlatTable
import Proof.Wire_3_5.FinalPass.HashBuild
import Proof.Wire_3_5.FinalPass.LiftR
import Proof.Wire_3_5.FinalPass.SampleEval
import Proof.Wire_3_5.FinalPass.TermThrEval
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixHashObjective
import Proof.Wire_3_5.UnionMachine.DecisionBridge
import Proof.Wire_3_5.UnionMachine.FrontGate
import StatementChecks.Theorem2_5_PreparedCircuits
import StatementChecks.Wire_3_5
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_c39848557d4002fa7ca286e2.parent
  (sym : ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l)
  (thr : ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.ThrLeafJ2 l)
  (hash : ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.HashLeafJ2 l)
  (c4 : ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes.C4Leaf l)
  (s5 : ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.Plan.FinalPassLeaf l)
  (fronts : ∀ l : NearCubicWires.WireExponent3_5.Literals, Σ e : ℕ, ∀ F : NearCubicWires.WireExponent3_5.Split.GateFree l, NearCubicWires.WireExponent3_5.Split.GateFreeOK l F → NearCubicWires.WireExponent3_5.UnionMachine.PlanW3.FrontsFWE3 e l F)
  : (NearCubicWires.WireExponent3_5.Literals → NearCubicWires.WireExponent3_5.rowB) :=
  NearCubicWires.WireExponent3_5.SplitRootTop3.rowB_root3 sym thr hash c4 s5 fronts
