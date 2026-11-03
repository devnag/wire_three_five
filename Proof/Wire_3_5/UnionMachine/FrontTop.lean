import Proof.Wire_3_5.UnionMachine.FrontRest
import Proof.Wire_3_5.UnionMachine.FrontPh2
import Proof.Wire_3_5.UnionMachine.FrontDecodeBase

/-! # C6 front, the whole front machine (P3:3669-3680)

The front at the union's call: the length gate (below the onset the rejecting bank), phase 1 (copy of `x`, the width
`1^q`, the oracle stage, the size verdict), three branches (the walker's scan, the oracle's decoding, the oracle's size;
each failing branch: the rejecting bank), phase 2 (the PCPP output word of the substituted circuit), and a branch on the
guess's mode tag into the chain after phase 2 at that mode (`FrontRest.restM`). **`topM`**; its runs:
**`top_gate`** (below the onset), **`top_rejO`**, **`top_rejF`**, **`top_rejV`** (a failing branch), **`top_rest`** (the
chain after phase 2, given its run at the tagged mode).

Paper quantity of the main type: the front's output bank on every input and witness. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf)

/-- Phase 1's fuel. -/
noncomputable def ph1C (k Ap G : ℕ) (xs w : List Bool) : ℕ :=
  (8 * xs.length + 14) + 1 + (FrontWidthCost.qCost k Ap xs + 1 +
    (FrontOracle.osCost xs w (Ledger.nativeWidth k Ap xs.length) + 1 +
      FrontSizeStage.ssCost xs (2 ^ RecoveryScheduleEnvelope.oracleDepth G)))

section Layout
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (htf : 1 ≤ tf) (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
  (k Ap G : ℕ) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + FrontPh2.PH2 source a k ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + FrontPh2.PH2 source a k) + FrontRest.RS m Dw Dl deg De Dt c ≤ tf)

/-- Phase 1's tapes. -/
noncomputable def q1 : Fin (NW P tf) := FrontPh1.qT P tf k 1 hp1
noncomputable def o1 (j : Fin FrontOracle.OS) : Fin (NW P tf) := FrontPh1.orT P tf k 1 hp1 j

end Layout

/-! ## The runs -/

/-- Phase 1's input facts (the lengths and the decoded oracle's size against the input). -/
structure Ph1OK (k Ap : ℕ) (xs w : List Bool) : Prop where
  hN : 2 ≤ xs.length
  hwl : 16 * w.length ≤ xs.length
  hℓ : natBitLength (Ledger.nativeWidth k Ap xs.length) ≤ xs.length + 1
  hq3 : 3 * natBitLength (Ledger.nativeWidth k Ap xs.length) ≤ Ledger.nativeWidth k Ap xs.length
  hsz1 : ∀ c : BooleanCircuit (Ledger.nativeWidth k Ap xs.length),
    CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length) (value (payload w.tail)) = some c →
      c.size + 1 ≤ 2 * xs.length + 2
  hsz2 : ∀ c : BooleanCircuit (Ledger.nativeWidth k Ap xs.length),
    CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length) (value (payload w.tail)) = some c →
      2 * natBitLength (Ledger.nativeWidth k Ap xs.length) + 2 * natBitLength c.size + 2 ≤ 2 * xs.length + 2

section Runs
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (htf : 1 ≤ tf) (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
  (k Ap G : ℕ) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + FrontPh2.PH2 source a k ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + FrontPh2.PH2 source a k) + FrontRest.RS m Dw Dl deg De Dt c ≤ tf)
  (C : ℕ) (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ)
  (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ)
open NearCubicWires.RepairSource.CloseoutFinal

/-- The state after the gate passes: pristine past the flag, `x` and `w` on the input tapes. -/
theorem pass_state {N : ℕ} (x : BitInput N) (w : List Bool) :
    PristineH P tf (fun _ => 0) (C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true) 1 ∧
      C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true (FrontPh1.xT P tf) =
        RepairOrdinary.frame (List.ofFn x) ∧
      C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true (FrontPh1.wT P tf) =
        RepairOrdinary.frame w := by
  have fv : (FrontGate.flagT P tf htf).val = 2 + NL P := rfl
  refine ⟨⟨fun y hy => ⟨?_, rfl⟩, fun i => ⟨?_, rfl⟩⟩, ?_, ?_⟩
  · have hne : y ≠ FrontGate.flagT P tf htf := fun e => by rw [e, fv] at hy; omega
    simp only [C10LengthGate.exitTapes, if_neg hne, entryA]
    rw [if_neg (by omega), if_neg (by omega)]
  · have hne : Plan.lp P tf i ≠ FrontGate.flagT P tf htf := fun e => by
      have := congrArg Fin.val e; rw [fv, FrontSlots.lp_val] at this; have := i.isLt; omega
    simp only [C10LengthGate.exitTapes, if_neg hne]
    exact FrontGate.entryA_lp P tf x w i
  · have hne : FrontPh1.xT P tf ≠ FrontGate.flagT P tf htf := fun e => by
      have := congrArg Fin.val e; rw [fv, FrontPh1.xT_val] at this; omega
    simp only [C10LengthGate.exitTapes, if_neg hne, entryA, FrontPh1.xT_val, if_true]
  · have hne : FrontPh1.wT P tf ≠ FrontGate.flagT P tf htf := fun e => by
      have := congrArg Fin.val e; rw [fv, FrontPh1.wT_val] at this; omega
    simp only [C10LengthGate.exitTapes, if_neg hne, entryA, FrontPh1.wT_val]
    simp

end Runs

/-! ## The chain after phase 2 -/

section RunRest
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.RepairOrdinary.CloseoutCaseTwo

end RunRest

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTop
