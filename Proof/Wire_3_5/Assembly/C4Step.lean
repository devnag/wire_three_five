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
import Proof.Wire_3_5.Assembly.C4Stage1
import Proof.Wire_3_5.Assembly.SymStageRoot
import Proof.Wire_3_5.Assembly.SymStageStepB
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_46ff96c04d4a39bb659376b8.parent
  (h : NearCubicWires.WireExponent3_5.C4Stage1.StageT)
  : ((l : NearCubicWires.WireExponent3_5.Literals) → NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes.C4Leaf l) :=
  NearCubicWires.WireExponent3_5.C4Stage1.pass h
