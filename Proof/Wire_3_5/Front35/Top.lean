import Proof.Wire_3_5.Front35.Ph2
import Proof.Wire_3_5.UnionMachine.FrontTop

/-!
# The front machine at the outer step

Paper v2, §H.5: the weak machine on a source word `z` of length `N` "guesses the two circuits `Γ_src` and `Γ_pf` above,
a class tag, and one sparse grid sum for each distinct PCPP variable. It rejects malformed descriptions [...] and it
rejects unless `Γ_src` passes the source check. Systematic parities are constructed from the PCPP output"; "At the
finitely many source lengths where this fixed envelope exceeds the refuter's `N/10` guess budget, the machine rejects
outright".

The front at the union's call: the length gate (below the onset the rejecting bank); phase 1 (the copy of `x`, the
width `1^q`, the old oracle stage: the tag, the walker's verdict and the rest of the guess); a branch on the walker's
verdict; phase 2 (`Ph2.ph2M`: the walk stage, the copy of `x`, the cold front end of the outer step); a branch on the
cold front end's verdict `Passes` (the dyadic length, the decoded pair within `q^G` gates, the `λ_a` guard and the source
check); a branch on the tag into the chain after phase 2 (`FrontRest.restM`) at the PCPP output word of `H_Γ`.
**`topM`**; its runs **`top_gate`** (below the onset), **`top_rejO`** (the walker's scan fails), **`top_rejP`** (the
outer step's guards fail), **`top_rest`** (the chain, given its run at the tagged mode).

Paper quantity of the main type: the front's output bank on every input and witness, at the PCPP output of `H_Γ`.
-/

set_option autoImplicit false
set_option maxRecDepth 120000

namespace NearCubicWires.WireExponent3_5.UnionMachine.Front35.Top

open _root_.NearCubicWires _root_.NearCubicWires.LocalBitMultitape _root_.NearCubicWires.RepairOrdinary
open _root_.NearCubicWires.ExtDecompositionBatch _root_.NearCubicWires.RepairRepresentation
open _root_.NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open _root_.NearCubicWires.WireExponent3_5 _root_.NearCubicWires.WireExponent3_5.Cost
open _root_.NearCubicWires.WireExponent3_5.FinalPass.Tm
open _root_.NearCubicWires.WireExponent3_5.UnionMachine _root_.NearCubicWires.WireExponent3_5.UnionMachine.Plan
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open _root_.NearCubicWires.RepairSource _root_.NearCubicWires.SourceInterfaces
open _root_.NearCubicWires.RepairOrdinary.RadixSemantics (value)
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf)
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontTop (q1 o1 ph1C Ph1OK pass_state)
open NearCubicGates.Close W3.NearCubicWires.RepairSource.Outer3 _root_.NearCubicWires.RepairSource.CloseoutFinal

section Layout
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (htf : 1 ≤ tf) {mw : Outer.MWSource} {kh : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (kh + 2))} {L : ℕ}
  {SV : Outer.SuccinctVerifier H L} {a : PointwisePCPPAlgorithm} {cutoff D degree copies : ℕ} {delta : ℚ}
  (CN : ColdNativeW mw SV a cutoff D degree copies delta)
  (k Ap G : ℕ) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + Ph2.PH2 CN ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + Ph2.PH2 CN) + FrontRest.RS m Dw Dl deg De Dt c ≤ tf)

/-- Phase 2's PCPP output word and verdict tapes. -/
noncomputable def po2 : Fin (NW P tf) := Ph2.poT P tf CN (1 + FrontPh1.PH1 k) hp2
noncomputable def fl2 : Fin (NW P tf) := Ph2.flT P tf CN (1 + FrontPh1.PH1 k) hp2

/-- The chain after phase 2 at mode `m`. -/
noncomputable def restAt (m : Mode) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56)
    (crT KT AT : ℕ) :=
  FrontRest.restM P tf m Dw Dl deg De Dt c (1 + FrontPh1.PH1 k + Ph2.PH2 CN) (hr m) (q1 P tf k hp1)
    (o1 P tf k hp1 13) (po2 P tf CN k hp2) Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT

/-- The branch on the tag. -/
noncomputable def mT (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  iteMachine (o1 P tf k hp1 14)
    (restAt P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Mode.thr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (restAt P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Mode.sym Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)

/-- After phase 2: the branch on the outer step's verdict. -/
noncomputable def mP (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  iteMachine (fl2 P tf CN k hp2)
    (mT P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) (FrontGate.rejM P tf)

/-- After phase 1: the branch on the walker's verdict, then phase 2. -/
noncomputable def mO (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ) :=
  iteMachine (o1 P tf k hp1 11)
    (Composition.machine (Ph2.ph2M P tf CN (1 + FrontPh1.PH1 k) hp2)
      (mP P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))
    (FrontGate.rejM P tf)

/-- **The front machine.** -/
noncomputable def topM (C : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56)
    (crT KT AT : ℕ) :=
  FrontGate.gateThen P tf htf C
    (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))

/-- Phase 2's fuel. -/
noncomputable def ph2C {N : ℕ} (x : BitInput N) (w : List Bool) : ℕ :=
  Walk.wkCost w + 1 + ((8 * (List.ofFn x).length + 14) + 1 + CN.budget N x (payload w.tail))

end Layout

/-! ## The runs -/

section Runs
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (htf : 1 ≤ tf) {mw : Outer.MWSource} {kh : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (kh + 2))} {L : ℕ}
  {SV : Outer.SuccinctVerifier H L} {a : PointwisePCPPAlgorithm} {cutoff D degree copies : ℕ} {delta : ℚ}
  (CN : ColdNativeW mw SV a cutoff D degree copies delta)
  (k Ap G : ℕ) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + Ph2.PH2 CN ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + Ph2.PH2 CN) + FrontRest.RS m Dw Dl deg De Dt c ≤ tf)
  (C : ℕ) (Kw Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ Ce Ct cr : ℕ) (Pw : WM 10 56) (crT KT AT : ℕ)

/-- **Below the onset**: the rejecting bank. -/
theorem top_gate {N : ℕ} (x : BitInput N) (w : List Bool) (hN : N < C) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf CN k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (2 * N + 1 + 1 + (3 + 1)) (fun _ => 0) (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  unfold topM
  exact FrontGate.gate_reject P tf htf C _ x w hN

/-- **The walker's scan fails** (past the onset): the rejecting bank. -/
theorem top_rejO {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = false) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf CN k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 + (3 + 1)) + 1)) (fun _ => 0) (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨pr, hx, hw⟩ := pass_state P tf htf x w
  obtain ⟨H1, A1, s1, p1, -, -, -, h11, -, -, -, -, -, -⟩ := FrontPh1.ph1_step P tf k Ap G 1 hp1 (List.ofFn x) w
    (fun _ => 0) _ pr hx rfl hw rfl h1.hN h1.hwl h1.hℓ h1.hq3 h1.hsz1 h1.hsz2
  obtain ⟨H2, A2, s2, hH2, hA2, -⟩ := FrontGate.rej_step P tf H1 A1 (fun i => (p1.2 i).2) (fun i => (p1.2 i).1)
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = false := by
    unfold o1; rw [h11.1, h11.2, hO]; rfl
  have sO := iteF (o1 P tf k hp1 11) (Composition.machine (Ph2.ph2M P tf CN (1 + FrontPh1.PH1 k) hp2)
      (mP P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))
    (FrontGate.rejM P tf) hb s2
  have sAcc := Step.seq s1 sO
  have sT := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ sAcc
  exact ⟨H2, A2, sT, hH2, hA2⟩

/-- Phase 1's run, then phase 2's run, on a passing scan: the state after phase 2. -/
theorem top_ph2 {N : ℕ} (x : BitInput N) (w : List Bool) (h1 : Ph1OK k Ap (List.ofFn x) w) :
    ∃ (H1 : Fin (NW P tf) → ℕ) (A1 : Fin (NW P tf) → List Bool) (H2 : Fin (NW P tf) → ℕ)
      (A2 : Fin (NW P tf) → List Bool),
      Step (FrontPh1.ph1M P tf k Ap G 1 hp1) (ph1C k Ap G (List.ofFn x) w) (fun _ => 0)
        (C10LengthGate.exitTapes (FrontGate.flagT P tf htf) (entryA x w) 0 true) H1 A1 ∧
      (A1 (o1 P tf k hp1 11) = [FrontOracleField.okOf w] ∧ H1 (o1 P tf k hp1 11) = 0) ∧
      Step (Ph2.ph2M P tf CN (1 + FrontPh1.PH1 k) hp2) (ph2C CN x w) H1 A1 H2 A2 ∧
      PristineH P tf H2 A2 (1 + FrontPh1.PH1 k + Ph2.PH2 CN) ∧
      H2 (fl2 P tf CN k hp2) = 0 ∧
      readTapeBit (A2 (fl2 P tf CN k hp2)) 0 = CN.passed (List.ofFn x) (payload w.tail) ∧
      (CN.passed (List.ofFn x) (payload w.tail) = true → ∀ Bg : Outer.OuterGuess (Outer.width mw SV N),
        Worker.Decodes (Outer.width mw SV N) (payload w.tail) Bg →
        let r := requestAt mw SV a (Nat.log 2 N) Bg
        A2 (po2 P tf CN k hp2) = pcppOutput r (a.output r) ∧ H2 (po2 P tf CN k hp2) = 0) ∧
      (A2 (FrontPh1.xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H2 (FrontPh1.xT P tf) = 0) ∧
      (A2 (q1 P tf k hp1) = List.replicate (Ledger.nativeWidth k Ap (List.ofFn x).length) true ∧
        H2 (q1 P tf k hp1) = 0) ∧
      (A2 (o1 P tf k hp1 13) = RepairOrdinary.frame (restOf w.tail) ∧ H2 (o1 P tf k hp1 13) = 0) ∧
      (A2 (o1 P tf k hp1 14) = [w.headD false] ∧ H2 (o1 P tf k hp1 14) = 0) := by
  obtain ⟨pr, hx, hw⟩ := pass_state P tf htf x w
  obtain ⟨H1, A1, s1, p1, hq1, h14, h13, h11, -, -, -, hx1, hw1, -⟩ := FrontPh1.ph1_step P tf k Ap G 1 hp1
    (List.ofFn x) w (fun _ => 0) _ pr hx rfl hw rfl h1.hN h1.hwl h1.hℓ h1.hq3 h1.hsz1 h1.hsz2
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  obtain ⟨H2, A2, s2, p2, f2H, f2A, c2, k2⟩ := Ph2.ph2_step P tf CN (1 + FrontPh1.PH1 k) hp2 x w
    (by have := h1.hwl; rw [hlen] at this; exact this) H1 A1 p1 hx1.1 hx1.2 hw1.1 hw1.2
  have vq := FrontPh1.qT_val P tf k 1 hp1
  have vo := FrontPh1.orT_val P tf k 1 hp1
  have hqo := (FrontWidth.qOut k).isLt
  have hPH1 : FrontPh1.PH1 k = 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST := rfl
  have kq := k2 (q1 P tf k hp1) (by unfold q1; rw [vq]; omega)
  have k13 := k2 (o1 P tf k hp1 13) (by unfold o1; rw [vo]; omega)
  have k14 := k2 (o1 P tf k hp1 14) (by unfold o1; rw [vo]; omega)
  have kx := k2 (FrontPh1.xT P tf) (by rw [FrontPh1.xT_val]; omega)
  refine ⟨H1, A1, H2, A2, s1, h11, s2, p2, f2H, f2A, c2, ?_, ?_, ?_, ?_⟩
  · rw [kx.1, kx.2]; exact hx1
  · rw [kq.1, kq.2]; exact hq1
  · rw [k13.1, k13.2]; exact h13
  · rw [k14.1, k14.2]; exact h14

/-- **The outer step's guards fail** (past the onset, the scan passes): the rejecting bank. -/
theorem top_rejP {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = true) (hp : CN.passed (List.ofFn x) (payload w.tail) = false) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf CN k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 + ((ph2C CN x w + 1 + (3 + 1)) + 1)) + 1)) (fun _ => 0)
        (entryA x w) H' A' ∧
      (∀ i, H' (Plan.lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A' (Plan.lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨H1, A1, H2, A2, s1, h11, s2, p2, f2H, f2A, -, -, -, -, -⟩ :=
    top_ph2 P tf htf CN k Ap G hp1 hp2 x w h1
  obtain ⟨H3, A3, s3, hH3, hA3, -⟩ := FrontGate.rej_step P tf H2 A2 (fun i => (p2.2 i).2) (fun i => (p2.2 i).1)
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = true := by
    rw [h11.1, h11.2, hO]; rfl
  have hb2 : readTapeBit (A2 (fl2 P tf CN k hp2)) (H2 (fl2 P tf CN k hp2)) = false := by
    rw [f2H, f2A, hp]
  have sP := iteF (fl2 P tf CN k hp2) (mT P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb2 s3
  have sO := iteT (o1 P tf k hp1 11) (Composition.machine (Ph2.ph2M P tf CN (1 + FrontPh1.PH1 k) hp2)
      (mP P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))
    (FrontGate.rejM P tf) hb (Step.seq s2 sP)
  have sT := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ (Step.seq s1 sO)
  exact ⟨H3, A3, sT, hH3, hA3⟩

/-- **The chain after phase 2** (past the onset, the scan and the outer step's guards pass): given the chain's run at
the tagged mode from the state after phase 2, the front's run. -/
theorem top_rest {N : ℕ} (x : BitInput N) (w : List Bool) (hN : C ≤ N) (h1 : Ph1OK k Ap (List.ofFn x) w)
    (hO : FrontOracleField.okOf w = true) (hp : CN.passed (List.ofFn x) (payload w.tail) = true)
    (Bg : Outer.OuterGuess (Outer.width mw SV N)) (hB : Worker.Decodes (Outer.width mw SV N) (payload w.tail) Bg)
    (m : Mode) (hm : m = FrontDecode.modeOf (w.headD false))
    (Q : (Fin (NW P tf) → ℕ) → (Fin (NW P tf) → List Bool) → Prop) (nR : ℕ)
    (hRest : ∀ (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool),
      PristineH P tf H A (1 + FrontPh1.PH1 k + Ph2.PH2 CN) →
      (A (FrontPh1.xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H (FrontPh1.xT P tf) = 0) →
      (A (q1 P tf k hp1) = List.replicate (Ledger.nativeWidth k Ap (List.ofFn x).length) true ∧
        H (q1 P tf k hp1) = 0) →
      (A (o1 P tf k hp1 13) = RepairOrdinary.frame (restOf w.tail) ∧ H (o1 P tf k hp1 13) = 0) →
      (A (po2 P tf CN k hp2) = pcppOutput (requestAt mw SV a (Nat.log 2 N) Bg)
          (a.output (requestAt mw SV a (Nat.log 2 N) Bg)) ∧ H (po2 P tf CN k hp2) = 0) →
      ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
        Step (restAt P tf CN k Dw Dl deg De Dt c hp1 hp2 hr m Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT) nR H A H' A' ∧
          Q H' A') :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (topM P tf htf CN k Ap G Dw Dl deg De Dt c hp1 hp2 hr C Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
        (4 * C + 1 + 1 + ((ph1C k Ap G (List.ofFn x) w + 1 + ((ph2C CN x w + 1 + ((nR + 1) + 1)) + 1)) + 1))
        (fun _ => 0) (entryA x w) H' A' ∧ Q H' A' := by
  obtain ⟨H1, A1, H2, A2, s1, h11, s2, p2, f2H, f2A, c2, hx2, hq2, h13, h14⟩ :=
    top_ph2 P tf htf CN k Ap G hp1 hp2 x w h1
  obtain ⟨H3, A3, sR, qR⟩ := hRest H2 A2 p2 hx2 hq2 h13 (c2 hp Bg hB)
  have hb : readTapeBit (A1 (o1 P tf k hp1 11)) (H1 (o1 P tf k hp1 11)) = true := by
    rw [h11.1, h11.2, hO]; rfl
  have hb2 : readTapeBit (A2 (fl2 P tf CN k hp2)) (H2 (fl2 P tf CN k hp2)) = true := by
    rw [f2H, f2A, hp]
  have sT : Step (mT P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
      (nR + 1) H2 A2 H3 A3 := by
    unfold mT
    cases hwt : w.headD false
    · have hms : m = Mode.sym := by rw [hm, hwt]; rfl
      subst hms
      have hbt : readTapeBit (A2 (o1 P tf k hp1 14)) (H2 (o1 P tf k hp1 14)) = false := by
        rw [h14.1, h14.2, hwt]; rfl
      exact iteF (o1 P tf k hp1 14) _ _ hbt sR
    · have hms : m = Mode.thr := by rw [hm, hwt]; rfl
      subst hms
      have hbt : readTapeBit (A2 (o1 P tf k hp1 14)) (H2 (o1 P tf k hp1 14)) = true := by
        rw [h14.1, h14.2, hwt]; rfl
      exact iteT (o1 P tf k hp1 14) _ _ hbt sR
  have sP := iteT (fl2 P tf CN k hp2) (mT P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)
    (FrontGate.rejM P tf) hb2 sT
  have sO := iteT (o1 P tf k hp1 11) (Composition.machine (Ph2.ph2M P tf CN (1 + FrontPh1.PH1 k) hp2)
      (mP P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT))
    (FrontGate.rejM P tf) hb (Step.seq s2 sP)
  have sTop := FrontGate.gate_pass P tf htf C (Composition.machine (FrontPh1.ph1M P tf k Ap G 1 hp1)
      (mO P tf CN k Dw Dl deg De Dt c hp1 hp2 hr Kw Kb Db cdf ζ Cδ Ce Ct cr Pw crT KT AT)) x w hN _ _ _ (Step.seq s1 sO)
  exact ⟨H3, A3, sTop, qR⟩

end Runs

end NearCubicWires.WireExponent3_5.UnionMachine.Front35.Top
