import Proof.Wire_3_5.UnionMachine.FrontRest
import Proof.Wire_3_5.UnionMachine.FrontPh2
import Proof.Wire_3_5.UnionMachine.FrontDecode

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
noncomputable def v1 : Fin (NW P tf) := FrontPh1.vT P tf k 1 hp1
/-- Phase 2's PCPP output word. -/
noncomputable def po2 : Fin (NW P tf) :=
  FrontPh2.poT P tf source a k (1 + FrontPh1.PH1 k) hp2 (o1 P tf k hp1 FrontOracle.descO)

/-- The chain after phase 2 at mode `m`. -/
noncomputable def restAt (m : Mode) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56)
    (crT KT AT : ℕ) :=
  FrontRest.restM P tf m Dw Dl deg De Dt c (1 + FrontPh1.PH1 k + FrontPh2.PH2 source a k) (hr m) (q1 P tf k hp1)
    (o1 P tf k hp1 13) (po2 P tf source a k hp1 hp2) Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT

/-- The branches after phase 1 (the size verdict, then phase 2 and the tag). -/
noncomputable def mV (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ)
    (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  iteMachine (v1 P tf k hp1)
    (Composition.machine (FrontPh2.ph2M P tf source a k (1 + FrontPh1.PH1 k) hp2 (q1 P tf k hp1)
        (o1 P tf k hp1 FrontOracle.descO) Hh Cpad)
      (iteMachine (o1 P tf k hp1 14)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)))
    (FrontGate.rejM P tf)

noncomputable def mF (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ)
    (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  iteMachine (o1 P tf k hp1 FrontOracle.flagO)
    (mV P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) (FrontGate.rejM P tf)

noncomputable def mO (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ)
    (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  iteMachine (o1 P tf k hp1 11)
    (mF P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) (FrontGate.rejM P tf)

/-- **The front machine.** -/
noncomputable def topM (C : ℕ) (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (Kw Kb Db : ℕ) (cdf : Bool)
    (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  FrontGate.gateThen P tf htf C
    (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))

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

/-- **Below the onset**: the rejecting bank. -/
theorem top_gate {N : ℕ} (x : BitInput N) (w : List Bool) (hN : N < C) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf source a k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (2 * N + 1 + 1 + (3 + 1)) (fun _ => 0) (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  unfold topM
  exact FrontGate.gate_reject P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN

/-- **The walker's scan fails** (past the onset): the rejecting bank. -/
theorem top_rejO {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = false) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf source a k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 + (3 + 1)) + 1)) (fun _ => 0) (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨pr, hx, hw⟩ := pass_state P tf htf x w
  obtain ⟨H1, A1, s1, p1, -, -, -, h11, -, -, -, -, -, -⟩ := FrontPh1.ph1_step P tf k Ap G 1 hp1 (List.ofFn x) w
    (fun _ => 0) _ pr hx rfl hw rfl h1.hN h1.hwl h1.hℓ h1.hq3 h1.hsz1 h1.hsz2
  obtain ⟨H2, A2, s2, hH2, hA2, -⟩ := FrontGate.rej_step P tf H1 A1 (fun i => (p1.2 i).2) (fun i => (p1.2 i).1)
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = false := by
    unfold o1; rw [h11.1, h11.2, hO]; rfl
  have sI := iteF (o1 P tf k hp1 11)
    (mF P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb s2
  have sO : Step (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) (3 + 1) H1 A1 H2 A2 := sI
  have sAcc : Step (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) (ph1C k Ap G (List.ofFn x) w + 1 + (3 + 1)) (fun _ => 0)
      (C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true) H2 A2 := Step.seq s1 sO
  have sT := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ sAcc
  refine ⟨H2, A2, ?_, hH2, hA2⟩
  unfold topM
  exact sT

/-- **The oracle does not decode** (past the onset, the scan passes): the rejecting bank. -/
theorem top_rejF {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = true)
    (hF : (CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap (List.ofFn x).length)
      (value (payload w.tail))).isSome = false) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf source a k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 + ((3 + 1) + 1)) + 1)) (fun _ => 0) (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨pr, hx, hw⟩ := pass_state P tf htf x w
  obtain ⟨H1, A1, s1, p1, -, -, -, h11, hfl, -, -, -, -, -⟩ := FrontPh1.ph1_step P tf k Ap G 1 hp1 (List.ofFn x) w
    (fun _ => 0) _ pr hx rfl hw rfl h1.hN h1.hwl h1.hℓ h1.hq3 h1.hsz1 h1.hsz2
  obtain ⟨H2, A2, s2, hH2, hA2, -⟩ := FrontGate.rej_step P tf H1 A1 (fun i => (p1.2 i).2) (fun i => (p1.2 i).1)
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = true := by
    unfold o1; rw [h11.1, h11.2, hO]; rfl
  have hb2 : readTapeBit (A1 (o1 P tf k hp1 FrontOracle.flagO)) (H1 (o1 P tf k hp1 FrontOracle.flagO)) = false := by
    unfold o1; rw [hfl.1, hfl.2, hF]; rfl
  have sF := iteF (o1 P tf k hp1 FrontOracle.flagO)
    (mV P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb2 s2
  have sI := iteT (o1 P tf k hp1 11)
    (mF P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb sF
  have sO : Step (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) ((3 + 1) + 1) H1 A1 H2 A2 := sI
  have sAcc : Step (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) (ph1C k Ap G (List.ofFn x) w + 1 + ((3 + 1) + 1)) (fun _ => 0)
      (C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true) H2 A2 := Step.seq s1 sO
  have sT := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ sAcc
  refine ⟨H2, A2, ?_, hH2, hA2⟩
  unfold topM
  exact sT

/-- **The oracle is too large** (past the onset, the scan passes, the oracle decodes): the rejecting bank. -/
theorem top_rejV {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = true)
    (hF : (CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap (List.ofFn x).length)
      (value (payload w.tail))).isSome = true)
    (hV : FrontSizeStage.sizeVerdict G (Ledger.nativeWidth k Ap (List.ofFn x).length)
      (CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap (List.ofFn x).length)
        (value (payload w.tail))) = false) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf source a k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 + (((3 + 1) + 1) + 1)) + 1)) (fun _ => 0) (entryA x w)
        H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨pr, hx, hw⟩ := pass_state P tf htf x w
  obtain ⟨H1, A1, s1, p1, -, -, -, h11, hfl, -, hv, -, -, -⟩ := FrontPh1.ph1_step P tf k Ap G 1 hp1 (List.ofFn x) w
    (fun _ => 0) _ pr hx rfl hw rfl h1.hN h1.hwl h1.hℓ h1.hq3 h1.hsz1 h1.hsz2
  obtain ⟨H2, A2, s2, hH2, hA2, -⟩ := FrontGate.rej_step P tf H1 A1 (fun i => (p1.2 i).2) (fun i => (p1.2 i).1)
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = true := by
    unfold o1; rw [h11.1, h11.2, hO]; rfl
  have hb2 : readTapeBit (A1 (o1 P tf k hp1 FrontOracle.flagO)) (H1 (o1 P tf k hp1 FrontOracle.flagO)) = true := by
    unfold o1; rw [hfl.1, hfl.2, hF]; rfl
  have hb3 : readTapeBit (A1 (v1 P tf k hp1)) (H1 (v1 P tf k hp1)) = false := by
    unfold v1; rw [hv.1, hv.2, hV]; rfl
  have sV := iteF (v1 P tf k hp1)
    (Composition.machine (FrontPh2.ph2M P tf source a k (1 + FrontPh1.PH1 k) hp2 (q1 P tf k hp1)
        (o1 P tf k hp1 FrontOracle.descO) Hh Cpad)
      (iteMachine (o1 P tf k hp1 14)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)))
    (FrontGate.rejM P tf) hb3 s2
  have sF := iteT (o1 P tf k hp1 FrontOracle.flagO)
    (mV P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb2 sV
  have sI := iteT (o1 P tf k hp1 11)
    (mF P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb sF
  have sO : Step (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) (((3 + 1) + 1) + 1) H1 A1 H2 A2 := sI
  have sAcc : Step (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) (ph1C k Ap G (List.ofFn x) w + 1 + (((3 + 1) + 1) + 1)) (fun _ => 0)
      (C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true) H2 A2 := Step.seq s1 sO
  have sT := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ sAcc
  refine ⟨H2, A2, ?_, hH2, hA2⟩
  unfold topM
  exact sT

end Runs

/-! ## The chain after phase 2 -/

section RunRest
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (htf : 1 ≤ tf) (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
  (k Ap G : ℕ) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + FrontPh2.PH2 source a k ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + FrontPh2.PH2 source a k) + FrontRest.RS m Dw Dl deg De Dt c ≤ tf)
  (C : ℕ) (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ)
  (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ)
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.RepairOrdinary.CloseoutCaseTwo

/-- Phase 2's fuel. -/
noncomputable def ph2C (hpad : k + 3 ≤ Cpad) {N : ℕ} (x : BitInput N) (q : ℕ)
    (hq : PCPPNativeHierarchyNodes.width source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x ≤ q)
    (O : BooleanCircuit q) : ℕ :=
  (8 * (List.ofFn x).length + 14) + 1 + (FrontHierarchy.hierCost k Hh.coefficient (List.ofFn x) (Hh.time N) + 1 +
    (FrontCapStage.capCost (List.ofFn x) q + 1 + ((2 * (q + 0) + 6) + 1 +
      obudgetG source a Hh Cpad hpad ⟨N, x⟩ hq O (FrontCapStage.capOf (List.ofFn x) q))))

/-- **The chain after phase 2** (past the onset; the scan passes, the oracle `O` decodes within its size): phase 2's
PCPP output word, then the chain at the guess's tagged mode (its run given as `hRest` from the state after phase 2). -/
theorem top_rest {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = true)
    (O : BooleanCircuit (Ledger.nativeWidth k Ap (List.ofFn x).length))
    (hdec : CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap (List.ofFn x).length)
      (value (payload w.tail)) = some O)
    (hV : FrontSizeStage.sizeVerdict G (Ledger.nativeWidth k Ap (List.ofFn x).length)
      (CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap (List.ofFn x).length)
        (value (payload w.tail))) = true)
    (hcoeff : Hh.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad)
    (hq : PCPPNativeHierarchyNodes.width source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x ≤
      Ledger.nativeWidth k Ap (List.ofFn x).length)
    (hcap : 64 * (O.size + Ledger.nativeWidth k Ap (List.ofFn x).length + 4) + 1 ≤
      FrontCapStage.capOf (List.ofFn x) (Ledger.nativeWidth k Ap (List.ofFn x).length))
    (m : Mode) (hm : m = FrontDecode.modeOf (w.headD false))
    (Q : (Fin (NW P tf) → ℕ) → (Fin (NW P tf) → List Bool) → Prop) (nR : ℕ)
    (hRest : ∀ (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool),
      PristineH P tf H A (1 + FrontPh1.PH1 k + FrontPh2.PH2 source a k) →
      (A (FrontPh1.xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H (FrontPh1.xT P tf) = 0) →
      (A (q1 P tf k hp1) = List.replicate (Ledger.nativeWidth k Ap (List.ofFn x).length) true ∧
        H (q1 P tf k hp1) = 0) →
      (A (o1 P tf k hp1 13) = RepairOrdinary.frame (restOf w.tail) ∧ H (o1 P tf k hp1 13) = 0) →
      (A (po2 P tf source a k hp1 hp2) = pcppOutput (PCPPRequestBoundary.request a
          (padSubstituted source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x hpad hq O))
          (a.output (PCPPRequestBoundary.request a
            (padSubstituted source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x hpad hq O))) ∧
        H (po2 P tf source a k hp1 hp2) = 0) →
      ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
        Step (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr m Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) nR H A H' A' ∧
          Q H' A') :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf source a k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 +
          ((((ph2C source a k Hh Cpad hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length) hq O + 1 + (nR + 1)) + 1) + 1)
            + 1)) + 1)) (fun _ => 0) (entryA x w) H' A' ∧ Q H' A' := by
  obtain ⟨pr, hx, hw⟩ := pass_state P tf htf x w
  obtain ⟨H1, A1, s1, p1, hq1, h14, h13, h11, hfl, hds, hv, hx1, -, hlow⟩ := FrontPh1.ph1_step P tf k Ap G 1 hp1
    (List.ofFn x) w (fun _ => 0) _ pr hx rfl hw rfl h1.hN h1.hwl h1.hℓ h1.hq3 h1.hsz1 h1.hsz2
  have vq := FrontPh1.qT_val P tf k 1 hp1
  have vo := FrontPh1.orT_val P tf k 1 hp1
  have hqo := (FrontWidth.qOut k).isLt
  have hdo : FrontOracle.descO ≠ (13 : Fin FrontOracle.OS) := by decide
  have hdo14 : FrontOracle.descO ≠ (14 : Fin FrontOracle.OS) := by decide
  have hne : ∀ a b : Fin (NW P tf), a.val ≠ b.val → a ≠ b := fun a b hab e => hab (congrArg Fin.val e)
  have hPH1 : FrontPh1.PH1 k = 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST := rfl
  -- phase 2
  obtain ⟨H2, A2, s2, p2, hpo, hx2, hq2, hlow2⟩ := FrontPh2.ph2_step P tf source a k (1 + FrontPh1.PH1 k) hp2
    (q1 P tf k hp1) (o1 P tf k hp1 FrontOracle.descO) Hh Cpad hcoeff hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length)
    hq O hcap H1 A1 p1 hx1.1 hx1.2 (by unfold q1; rw [vq]; constructor <;> omega) hq1.1 hq1.2
    (by unfold o1; rw [vo]; have := FrontOracle.descO.isLt; constructor <;> omega) (hds.1 O hdec) hds.2
    (hne _ _ (by unfold q1 o1; rw [vq, vo]; have := FrontOracle.descO.isLt; omega))
  have k13 := hlow2 (o1 P tf k hp1 13) (by unfold o1; rw [vo]; omega) (by unfold o1; rw [vo]; omega)
    (fun e => hdo.symm (by unfold o1 at e; exact (FrontSlots.rg_inj P tf _ _ e)))
  have k14 := hlow2 (o1 P tf k hp1 14) (by unfold o1; rw [vo]; omega) (by unfold o1; rw [vo]; omega)
    (fun e => hdo14.symm (by unfold o1 at e; exact (FrontSlots.rg_inj P tf _ _ e)))
  obtain ⟨H3, A3, sR, qR⟩ := hRest H2 A2 p2 hx2 hq2 ⟨by rw [k13.1]; exact h13.1, by rw [k13.2]; exact h13.2⟩ hpo
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = true := by
    unfold o1; rw [h11.1, h11.2, hO]; rfl
  have hb2 : readTapeBit (A1 (o1 P tf k hp1 FrontOracle.flagO)) (H1 (o1 P tf k hp1 FrontOracle.flagO)) = true := by
    unfold o1; rw [hfl.1, hfl.2, hdec]; rfl
  have hb3 : readTapeBit (A1 (v1 P tf k hp1)) (H1 (v1 P tf k hp1)) = true := by
    unfold v1; rw [hv.1, hv.2, hV]; rfl
  have sT : Step (iteMachine (o1 P tf k hp1 14)
      (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))
      (nR + 1) H2 A2 H3 A3 := by
    cases hwt : w.headD false
    · have hms : m = Mode.sym := by rw [hm, hwt]; rfl
      subst hms
      have hbt : readTapeBit (A2 (o1 P tf k hp1 14)) (H2 (o1 P tf k hp1 14)) = false := by
        rw [k14.1, k14.2]; unfold o1; rw [h14.1, h14.2, hwt]; rfl
      exact iteF (o1 P tf k hp1 14)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) hbt sR
    · have hms : m = Mode.thr := by rw [hm, hwt]; rfl
      subst hms
      have hbt : readTapeBit (A2 (o1 P tf k hp1 14)) (H2 (o1 P tf k hp1 14)) = true := by
        rw [k14.1, k14.2]; unfold o1; rw [h14.1, h14.2, hwt]; rfl
      exact iteT (o1 P tf k hp1 14)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) hbt sR
  have sP : Step (Composition.machine (FrontPh2.ph2M P tf source a k (1 + FrontPh1.PH1 k) hp2 (q1 P tf k hp1)
        (o1 P tf k hp1 FrontOracle.descO) Hh Cpad)
      (iteMachine (o1 P tf k hp1 14)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)))
      (ph2C source a k Hh Cpad hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length) hq O + 1 + (nR + 1))
      H1 A1 H3 A3 := Step.seq s2 sT
  have sV : Step (mV P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      ((ph2C source a k Hh Cpad hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length) hq O + 1 + (nR + 1)) + 1)
      H1 A1 H3 A3 :=
    iteT (v1 P tf k hp1)
      (Composition.machine (FrontPh2.ph2M P tf source a k (1 + FrontPh1.PH1 k) hp2 (q1 P tf k hp1)
          (o1 P tf k hp1 FrontOracle.descO) Hh Cpad)
        (iteMachine (o1 P tf k hp1 14)
          (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
          (restAt P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)))
      (FrontGate.rejM P tf) hb3 sP
  have sF : Step (mF P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      (((ph2C source a k Hh Cpad hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length) hq O + 1 + (nR + 1)) + 1) + 1)
      H1 A1 H3 A3 :=
    iteT (o1 P tf k hp1 FrontOracle.flagO)
      (mV P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      (FrontGate.rejM P tf) hb2 sV
  have sO : Step (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      ((((ph2C source a k Hh Cpad hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length) hq O + 1 + (nR + 1)) + 1) + 1)
        + 1) H1 A1 H3 A3 :=
    iteT (o1 P tf k hp1 11)
      (mF P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      (FrontGate.rejM P tf) hb sF
  have sAcc : Step (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))
      (ph1C k Ap G (List.ofFn x) w + 1 +
        ((((ph2C source a k Hh Cpad hpad x (Ledger.nativeWidth k Ap (List.ofFn x).length) hq O + 1 + (nR + 1)) + 1) + 1)
          + 1)) (fun _ => 0)
      (C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true) H3 A3 := Step.seq s1 sO
  have sTop := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf source a k Dw Dl deg De Dt c hp1 hp2 hr Hh Cpad Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ sAcc
  refine ⟨H3, A3, ?_, qR⟩
  unfold topM
  exact sTop

end RunRest

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTop
