import Proof.Rows.RowsMaskGeneric
import Proof.Rows.RowsSymBounds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.BankNF
open Lean Meta Elab Tactic

def leaves : List Name := [``NearCubicWires.RepairOrdinary.frame, ``List.replicate, ``HAppend.hAppend,
  ``List.append, ``List.flatMap, ``List.ofFn, ``NearCubicWires.RepairOrdinary.ZeroPadding.pad, ``List.cons,
  ``List.nil, ``NearCubicWires.RepairRepresentation.natWord,
  ``NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word,
  ``NearCubicWires.RepairOrdinary.UnaryTemplate.tape, ``NearCubicWires.RepairOrdinary.SignedSortKey.binary,
  ``PCJ45bee56da9f34d5a_NativeFamilyFlags.source]

def natUnfold : List Name := [``PCJ45bee56da9f34d5a_CircuitPowerInput.caps,
  ``PCJ45bee56da9f34d5a_SelectedPowerBank.caps, ``PCJ45bee56da9f34d5a_PowerBank.factorCap,
  ``PCJ45bee56da9f34d5a_CircuitFlagBank.caps]

def decideBranch (e : Expr) : MetaM (Option Expr) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isConstOf ``ite && args.size == 5 then
    let inst ← whnf args[2]!
    if inst.isAppOf ``Decidable.isTrue then return some args[3]!
    if inst.isAppOf ``Decidable.isFalse then return some args[4]!
  if f.isConstOf ``dite && args.size == 5 then
    let inst ← whnf args[2]!
    if inst.isAppOf ``Decidable.isTrue then return some (mkApp args[3]! inst.appArg!)
    if inst.isAppOf ``Decidable.isFalse then return some (mkApp args[4]! inst.appArg!)
  return none

def natNorm (e : Expr) : MetaM Expr := do
  match e.getAppFn with
  | .const n _ =>
    if natUnfold.contains n then
      let some e' ← unfoldDefinition? e | return e
      let e' ← whnfCore e'
      match ← decideBranch e' with
      | some b => return b.headBeta
      | none => return e
    else return e
  | _ => return e

partial def norm (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then return e
  let e ← whnfCore e
  match e.getAppFn with
  | .const n _ =>
    if leaves.contains n then
      let args ← e.getAppArgs.mapM fun a => do
        let ty ← inferType a
        if ty.isAppOfArity ``List 1 && ty.appArg!.isConstOf ``Bool then norm a (fuel-1)
        else natNorm a
      return mkAppN e.getAppFn args
    match ← decideBranch e with
    | some b => return (← norm b (fuel-1))
    | none =>
    match ← unfoldDefinition? e with
    | some e' => norm e' (fuel-1)
    | none =>
      match ← reduceMatcher? e with
      | ReduceMatcherResult.reduced e' => norm e' (fuel-1)
      | _ => return e
  | _ => return e

/-- `bank_nf c`: rewrite the first full application of the bank `c` in the goal to its evaluated form. -/
elab "bank_nf " c:ident : tactic => withMainContext do
  let cname ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo c
  let ar := (← getConstInfo cname).type.getForallArity
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun s => s.isAppOf cname && s.getAppNumArgs == ar)
    | throwError "bank_nf: no full application of {cname}"
  let nf ← norm e 2000
  let heq ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e nf)
  let r ← (← getMainGoal).rewrite tgt heq
  let g ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g :: r.mvarIds)

end RowsConstruction.BankNF

namespace RowsConstruction.BaseLayout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination
open RowsConstruction.ThrCell RowsConstruction.MaskGeneric NearCubicWires.SupplierWalkBridge
noncomputable section

/-! ## 1. The four THR parameter functions of `(q, |input|)` (`ThrBounds.thr_numeric`) -/


/-! ## 2. Loop sizes -/


/-! ## 3. The THR census: every traversal input word, port by port -/

/-! ## 4. The THR master bank of a row key -/

/-! ## 5. The THR row's mask loop on its own masters: the family row's selector -/

/-! ## 6. SYM: parameters, census, masters, and the row's mask loop -/


section Sym

end Sym

/-! ## 7. The reserves the initializer computes (`UnaryCalc.value` of the unary `q+|input|`) -/




section Ports
end Ports

section ThrBase

end ThrBase

section SymBase

end SymBase

end
end RowsConstruction.BaseLayout
