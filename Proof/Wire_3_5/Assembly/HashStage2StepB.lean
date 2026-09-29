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
import Proof.Wire_3_5.Assembly.HashFinish
import Proof.Wire_3_5.Assembly.HashStage2StepA
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_4934cec25217d8b596812df0.parent

  : (NearCubicWires.WireExponent3_5.HashStage2.StageT) :=
  let h : (
    NearCubicWires.WireExponent3_5.HashStage2.StageT
  ) := (
    NearCubicWires.WireExponent3_5.HashFinish.hashFinal
  );
  (@PCConstruction_6f0183586ab63d9a1d3a3b27.parent h)
