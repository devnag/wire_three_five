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
import Proof.Wire_3_5.Assembly.HRootB
import Proof.Wire_3_5.Assembly.HStepE
import Proof.Wire_3_5.Assembly.HStepH
import Proof.Wire_3_5.Assembly.HStepK
import Proof.Wire_3_5.FinalPass.Stage5
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_0e5eb99feeb25a1b9e58782b.parent
  (h : NearCubicWires.WireExponent3_5.FinalPassStage5.StageT)
  : (NearCubicWires.WireExponent3_5.FinalPassStage4.StageT) :=
  NearCubicWires.WireExponent3_5.FinalPassStage5.pass h
