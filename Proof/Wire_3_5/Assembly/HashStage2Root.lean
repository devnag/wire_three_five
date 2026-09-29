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
import Proof.Wire_3_5.Assembly.RootStep
set_option linter.unusedVariables false
set_option linter.defProp false
namespace PCRootPrefix_b353c5238d2006956ce747179d7901e6119abbd855b5e69b02bf1fd6b5c71b67
set_option maxHeartbeats 4000000 in
noncomputable def root
    (sym : ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l)
    (thr : (l : NearCubicWires.WireExponent3_5.Literals) →
      NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l →
        NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.ThrLeafJ2 l)
    (hash : (l : NearCubicWires.WireExponent3_5.Literals) →
      NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l →
        NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.HashLeafJ2 l)
    (c4 : (l : NearCubicWires.WireExponent3_5.Literals) → NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes.C4Leaf l)
    (s5 : (l : NearCubicWires.WireExponent3_5.Literals) → NearCubicWires.WireExponent3_5.PrimAsm.Plan.FinalPassLeaf l)
    (fronts : (l : NearCubicWires.WireExponent3_5.Literals) →
      @Sigma.{0, 0} Nat fun e =>
        (F : NearCubicWires.WireExponent3_5.Split.GateFree l) →
          NearCubicWires.WireExponent3_5.Split.GateFreeOK l F →
            NearCubicWires.WireExponent3_5.UnionMachine.PlanW3.FrontsFWE3 e l F)
    : NearCubicWires.WireExponent3_5.Literals → NearCubicWires.WireExponent3_5.rowB :=
  (
    (@PCConstruction_c39848557d4002fa7ca286e2.parent sym thr hash c4 s5 fronts)
  )
end PCRootPrefix_b353c5238d2006956ce747179d7901e6119abbd855b5e69b02bf1fd6b5c71b67
