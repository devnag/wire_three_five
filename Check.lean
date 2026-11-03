import MainTheorem_Wire_3_5
open Lean Elab Command

/-! Run after `lake build`:  lake env lean Check.lean
It prints row B of the paper's Theorem 1.1 and Theorem 1.1 on the cone above row B, written out in Lean, the two main
theorems, their axioms, the lists of their hypotheses, and PASS or FAIL for each. -/

-- (a) Row B of Theorem 1.1 and the cone above it, with every definition of `Statement_Wire_3_5.lean` expanded.
#print NearCubicWires.WireExponent3_5.rowB
#print NearCubicWires.WireExponent3_5.rowBCone
#print NearCubicWires.WireExponent3_5
#print NearCubicWires.WireExponent3_5.WireExponent3_5Hard

-- (b) The main theorems: published statements ⇒ row B, and the same statements ⇒ Theorem 1.1 for every
-- `0 < c ≤ 1/8`, `K_T ≥ 11/2`, `K_S ≥ 9/2`.
#check @NearCubicWires.WireExponent3_5.rowB_from_literature
#check @NearCubicWires.WireExponent3_5.rowBCone_from_literature

-- (c) Their axioms. An unfinished proof would list `sorryAx` here.
#print axioms NearCubicWires.WireExponent3_5.rowB_from_literature
#print axioms NearCubicWires.WireExponent3_5.rowBCone_from_literature

/-- The hypotheses of a statement `∀ (h₁ : A₁) … (hₖ : Aₖ), B`, outermost first. -/
partial def checkBinderTypes : Expr → List Expr
  | .forallE _ t b _ => t :: checkBinderTypes b
  | _ => []

/-- The body `B` of a statement `∀ (h₁ : A₁) … (hₖ : Aₖ), B`. -/
partial def checkConclusion : Expr → Expr
  | .forallE _ _ b _ => checkConclusion b
  | e => e

/-- These are the only assumptions. Each is defined in `Statement.lean` or `Statement_Wire_3_5.lean`, with the
published sentence it transcribes. -/
def checkHypotheses : List Name := [
  `NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2,
  `NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2,
  `NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4,
  `NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2,
  `NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314,
  `NearCubicWires.Bindings.MW20.MW20_OracleCircuitPCP_TM2,
  `NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2,
  `NearCubicWires.WireExponent3_5.CLW20_Theorem1_13_Poly,
  `NearCubicWires.WireExponent3_5.CLW20_Lemma3_9_TM2_Large]

/-- PASS only if the hypotheses of `thm` are exactly `checkHypotheses`, in this order, its conclusion is `target`,
and its axioms are among Lean's standard three. -/
def checkMain (thm target : Name) : CommandElabM Unit := do
  let axs ← liftCoreM <| collectAxioms thm
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  let some info := (← getEnv).find? thm | throwError "FAIL: theorem not found"
  let binders := checkBinderTypes info.type
  let found := binders.map fun t => (t.constName?).getD Name.anonymous
  for h in found do
    IO.println s!"assumes: {h}"
  let okHyps := binders.all (·.isConst) && found == checkHypotheses
  let okConcl := (checkConclusion info.type).isConstOf target
  let okAxioms := axs.all std.contains
  if okHyps && okConcl && okAxioms then
    IO.println s!"PASS: {thm} proves {target} from the {checkHypotheses.length} hypotheses above and depends only on {axs.toList}"
  else
    throwError "FAIL: hypotheses as listed: {okHyps}; conclusion is {target}: {okConcl}; axioms {axs.toList}"

-- (d) Row B.
run_cmd checkMain ``NearCubicWires.WireExponent3_5.rowB_from_literature ``NearCubicWires.WireExponent3_5.rowB

-- (e) Theorem 1.1 on the cone above row B, from the same hypotheses.
run_cmd checkMain ``NearCubicWires.WireExponent3_5.rowBCone_from_literature ``NearCubicWires.WireExponent3_5.rowBCone
