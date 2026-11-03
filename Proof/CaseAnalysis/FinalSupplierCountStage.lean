import Proof.Amplification.RecoveryTapeSupport
import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmRetained
import Proof.CaseAnalysis.FinalSiteBodyUniform
import Proof.CaseAnalysis.RowsEstimatorActual
import Proof.CaseAnalysis.RowsEstimatorPrepareCopy
import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.MachineModel.Runs
import Proof.CaseAnalysis.FinalDividerDock
import Proof.CaseAnalysis.FinalSupplierWidth

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10DividerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The model fact: no `Step` ever blanks a tape -/

/-! ## §2 The bank on its scratch band -/

/-- On the scratch band the bank IS the scratch, by tape number. -/
theorem bank_scratch_apply {t : ℕ} (stream count driver input witness : List Bool)
    (s : ℕ → List Bool) (i : Fin t) (hi : 278 ≤ i.val) :
    bank stream count driver input witness s i = s i.val := by
  show bankAt stream count driver input witness s i.val = s i.val
  unfold bankAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos hi]

/-! ## §3 Why `Appends`'s `∀ s` forecloses the whole docked-engine library -/

/-! ## §4 The bank lift: a docked stage on the band IS a round step -/

/-- The scratch function read off an ambient bank-width tape function. -/
noncomputable def scratchOf (extra : ℕ) (A : Fin (218 + (60 + extra)) → List Bool)
    (s : ℕ → List Bool) : ℕ → List Bool :=
  fun v => if h : v < 218 + (60 + extra) then A ⟨v, h⟩ else s v

theorem scratchOf_apply (extra : ℕ) (A : Fin (218 + (60 + extra)) → List Bool)
    (s : ℕ → List Bool) (i : Fin (218 + (60 + extra))) :
    scratchOf extra A s i.val = A i := by
  unfold scratchOf
  rw [dif_pos i.isLt]

/-- **A tape function that agrees with a bank below `278` IS a bank.**  This is
the frame clause of the scratch band, and it is what lets a docked stage's exit
be read back as a round bank rather than as an opaque tape function. -/
theorem bank_of_agree_below (extra : ℕ) (stream count driver input witness : List Bool)
    (s : ℕ → List Bool) (A : Fin (218 + (60 + extra)) → List Bool)
    (hoff : ∀ i : Fin (218 + (60 + extra)), i.val < 278 →
      A i = bank stream count driver input witness s i) :
    A = bank stream count driver input witness (scratchOf extra A s) := by
  funext i
  by_cases h : i.val < 278
  · rw [hoff i h]
    show bankAt stream count driver input witness s i.val
      = bankAt stream count driver input witness (scratchOf extra A s) i.val
    unfold bankAt
    split_ifs <;> first | rfl | omega
  · rw [bank_scratch_apply stream count driver input witness (scratchOf extra A s) i
      (Nat.le_of_not_lt h)]
    exact (scratchOf_apply extra A s i).symm

/-- An exit head function that is pointwise zero is the parked head function. -/
theorem step_heads_parked {t s : ℕ} {M : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A B : Fin t → List Bool} (h : Step M n H A H' B) (hz : ∀ i, H' i = 0) :
    Step M n H A (fun _ => 0) B := by
  have he : H' = fun _ => 0 := funext hz
  rwa [he] at h

/-- **Any docked stage whose slots lie on the scratch band is a round step.**  The
stage's own frame clause `∀ i, (∀ j, slots j ≠ i) → A' i = A i` plus
`hband` gives agreement below `278`, and `bank_of_agree_below` reads the exit back
as a bank.  This is the lemma that makes the corpus's docked-engine library usable
inside a round -- once the band is blank, which §3 says `Appends` never is. -/
theorem round_step_of_dock (extra : ℕ) {ts r : ℕ} {M : Machine (218 + (60 + extra)) ts}
    (fuel : ℕ) (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (slots : Fin r → Fin (218 + (60 + extra))) (hband : ∀ j, 278 ≤ (slots j).val)
    (H' : Fin (218 + (60 + extra)) → ℕ) (A' : Fin (218 + (60 + extra)) → List Bool)
    (hstep : Step M fuel (fun _ => 0) (bank stream count driver input witness s) H' A')
    (hzero : ∀ i, H' i = 0)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      A' i = bank stream count driver input witness s i) :
    Step M fuel (fun _ => 0) (bank stream count driver input witness s) (fun _ => 0)
      (bank stream count driver input witness (scratchOf extra A' s)) := by
  have hoff : ∀ i : Fin (218 + (60 + extra)), i.val < 278 →
      A' i = bank stream count driver input witness s i := by
    intro i hi
    refine hframe i (fun j hj => ?_)
    have := hband j
    rw [hj] at this
    omega
  have hb := bank_of_agree_below extra stream count driver input witness s A' hoff
  rw [← hb]
  exact step_heads_parked hstep hzero

/-! ## §4b The discipline itself: a blank band above a moving line -/

/-- **The scratch discipline a round machine can actually maintain.**  The band is
blank from `line` up.  Contrast a LENGTH BOUND, which `round_band_dirty_persists`
(§3) shows buys nothing: no round can shorten what it received, so the only
invariant a round can restore is blankness of tapes it has not yet touched. -/
def BlankFrom (line : ℕ) (s : ℕ → List Bool) : Prop := ∀ v, line ≤ v → s v = []

/-! ## §5 The answer channel, on the bank

`answer` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is
`rowAnswer rows arity factors * denominator arity scale / rowDenominator rows arity factors`
-- A.13.9's ratio (`paper.tex:3158-3166`) carried to the uniform denominator. -/

/-! ## §6 The residual that composes -/

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

def Rounds (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop) : Prop :=
  ∀ (k : ℕ) (s : ℕ → List Bool), Inv k s →
    ∃ s' : ℕ → List Bool, Inv (k + 1) s' ∧
      Step body cost (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s k)
        (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness s' (k + 1))

/-- **The per-round choices, chained with the invariant carried along.**  The only
place a choice principle enters this module. -/
theorem chain_of_rounds (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (hrounds : Rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv)
    (w : ℕ → List Bool) (hw : Inv 0 w) :
    ∃ scratch : ℕ → ℕ → List Bool, scratch 0 = w ∧
      ∀ k : ℕ, Step body cost (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness (scratch k) k)
        (fun _ => 0)
        (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness (scratch (k + 1)) (k + 1)) := by
  classical
  have hchoice : ∀ (k : ℕ) (s : ℕ → List Bool), ∃ s' : ℕ → List Bool,
      Inv k s → Inv (k + 1) s' ∧
        Step body cost (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s k)
          (fun _ => 0)
          (roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
            input witness s' (k + 1)) := by
    intro k s
    by_cases hk : Inv k s
    · obtain ⟨s', hinv, hstep⟩ := hrounds k s hk
      exact ⟨s', fun _ => ⟨hinv, hstep⟩⟩
    · exact ⟨s, fun hc => absurd hc hk⟩
  choose g hg using hchoice
  refine ⟨fun k => Nat.rec (motive := fun _ => ℕ → List Bool) w (fun j b => g j b) k, rfl, ?_⟩
  have hinv : ∀ k : ℕ,
      Inv k (Nat.rec (motive := fun _ => ℕ → List Bool) w (fun j b => g j b) k) := by
    intro k
    induction k with
    | zero => exact hw
    | succ k ih => exact ((hg k _) ih).1
  intro k
  exact ((hg k _) (hinv k)).2

theorem callsReady_of_rounds (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hrounds : Rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv)
    (hpre : ∃ w : ℕ → List Bool, Inv 0 w ∧
      Step pre preFuel (fun _ => 0)
        (bank [] [] [] input witness (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))) :
    C10SupplierStage.CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness := by
  obtain ⟨w, hw, hstep⟩ := hpre
  obtain ⟨scratch, hs0, hchain⟩ :=
    chain_of_rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv hrounds w hw
  refine C10EnvelopeCounter.callsReady_at_clauseWidth extra pre body answer denominator phase
    pcpp coordinate systematicAtom entryWidth callCount preFuel cost clauseDegree q input witness
    (fun _ => fun _ => 0) scratch hlen hfit ?_ ?_ ?_
  · show Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (motive := fun _ => List Bool)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))
    rw [loopBank_roundBank, hs0, roundBank_zero]
    exact hstep
  · intro address _
    simpa only [loopBank_roundBank] using hchain address
  · intro address _ _
    simpa only [loopBank_roundBank] using hchain address


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
