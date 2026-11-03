import Proof.CaseAnalysis.FinalBandRecycle
import Proof.CaseAnalysis.FinalEnvelopeCounter

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage (CallsReady)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The cursor word -/

/-- **The cursor.**  A fixed-width binary word carrying the SATURATING round
index `min k envelope`.  `fixedWidthNatBits`
(`Proof/Foundations/OperationalWilliamsSourceCore.lean`) is
`List.ofFn fun bit : Fin width => value.testBit bit.val`, so the tape holds
exactly `width` cells whatever `k` is. -/
def cursorWord (width envelope k : ℕ) : List Bool :=
  WilliamsPublishedForm.fixedWidthNatBits width (min k envelope)

/-- **The cursor tape has the same length at every round.**  This is the whole
cost argument in one line: no round has to lengthen the cursor tape, so
`length_mono` (`Proof/CaseAnalysis/FinalNativeReload.lean`) costs nothing here
and the per-round charge is a function of `width` and not of `k`. -/
theorem cursorWord_length (width envelope k : ℕ) :
    (cursorWord width envelope k).length = width := by
  simp [cursorWord, WilliamsPublishedForm.fixedWidthNatBits]

/-- **Past the envelope the cursor stops moving.**  This is what makes the tail
of `Rounds` a SINGLE `k`-free obligation instead of a family. -/
theorem cursorWord_saturate (width envelope k : ℕ) (hk : envelope ≤ k) :
    cursorWord width envelope k = cursorWord width envelope envelope := by
  unfold cursorWord
  rw [min_eq_right hk, min_self]

theorem cursorWord_zero (width envelope : ℕ) :
    cursorWord width envelope 0 = ZeroPadding.pad width [] := by
  rw [CloseoutFinalC10BandRecycle.pad_nil]
  unfold cursorWord WilliamsPublishedForm.fixedWidthNatBits
  simp

/-- A fixed-width binary word determines its value below the width's capacity. -/
theorem fixedWidthNatBits_inj {width a b : ℕ} (ha : a < 2 ^ width) (hb : b < 2 ^ width)
    (h : WilliamsPublishedForm.fixedWidthNatBits width a
      = WilliamsPublishedForm.fixedWidthNatBits width b) : a = b := by
  unfold WilliamsPublishedForm.fixedWidthNatBits at h
  have hfun : (fun bit : Fin width => a.testBit bit.val)
      = fun bit : Fin width => b.testBit bit.val := List.ofFn_inj.mp h
  refine Nat.eq_of_testBit_eq (fun i => ?_)
  by_cases hi : i < width
  · simpa using congrFun hfun ⟨i, hi⟩
  · have hp : (2 : ℕ) ^ width ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hp)]

/-- **Below the envelope the cursor determines the round.**  No hypothesis on
any site polynomial, in contrast with `addressDeterminacy_of_nonempty`
(`Proof/CaseAnalysis/FinalRoundEmitter.lean`). -/
theorem cursorWord_inj (width envelope : ℕ) (hw : envelope < 2 ^ width) {k₁ k₂ : ℕ}
    (h₁ : k₁ ≤ envelope) (h₂ : k₂ ≤ envelope)
    (h : cursorWord width envelope k₁ = cursorWord width envelope k₂) : k₁ = k₂ := by
  unfold cursorWord at h
  have hm : min k₁ envelope = min k₂ envelope :=
    fixedWidthNatBits_inj (lt_of_le_of_lt (min_le_right _ _) hw)
      (lt_of_le_of_lt (min_le_right _ _) hw) h
  rwa [min_eq_left h₁, min_eq_left h₂] at hm

/-! ## §2 The envelope the paper names, and the width it needs -/

/-- **The paper's branch-independent address count.**  `paper.tex:4516`:
"which is exactly \(\log_2M\) for \(M=2^{\lceil d_G\log_2(q+2)\rceil}\)".  It is
the same number `callsReady_at_clauseWidth`
(`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`) makes the prologue count out
and `counter_length` (`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`)
measures. -/
def clauseEnvelope (clauseDegree q : ℕ) : ℕ := 2 ^ clauseWidth clauseDegree q

/-- **The cursor's tape width**: one cell more than `paper.tex:4516`'s
`\log_2 M`, so that the SATURATED value `clauseEnvelope` itself is representable. -/
def cursorWidth (clauseDegree q : ℕ) : ℕ := clauseWidth clauseDegree q + 1

/-- The width is enough for every value the cursor ever holds. -/
theorem clauseEnvelope_lt (clauseDegree q : ℕ) :
    clauseEnvelope clauseDegree q < 2 ^ cursorWidth clauseDegree q := by
  have h : 1 ≤ 2 ^ clauseWidth clauseDegree q := Nat.one_le_pow _ 2 (by omega)
  unfold clauseEnvelope cursorWidth
  rw [pow_succ]
  omega

/-! ## §3 The cost of the unary alternative, measured -/

def unaryCursorCost : ℕ → ℕ
  | 0 => 0
  | k + 1 => unaryCursorCost k + (2 * k + 2)

/-- **A unary cursor is QUADRATIC in the round count.**  Over the paper's
envelope `E = 2 ^ clauseWidth clauseDegree q` that is `E²`-sized -- a second
residual factor, which `ENDGAME_RESOURCE.md` §2 forbids outright, and in any
case unrepresentable in `Rounds`, whose per-round budget `cost` does not depend
on `k`.  `cursorWord_length` is the contrast. -/
theorem unaryCursorCost_eq (E : ℕ) : unaryCursorCost E = E * (E + 1) := by
  induction E with
  | zero => rfl
  | succ n ih =>
      unfold unaryCursorCost
      rw [ih]
      ring

/-! ## §4 The invariant -/

def CursorInv (width envelope cursorTape : ℕ) (Rest : (ℕ → List Bool) → Prop)
    (k : ℕ) (s : ℕ → List Bool) : Prop :=
  s cursorTape = cursorWord width envelope k ∧ Rest s

/-- **Writing the cursor onto a scratch.**  Used both to inhabit the invariant
and to show it does not disturb a band above `line`. -/
def setCursor (cursorTape : ℕ) (w : List Bool) (s : ℕ → List Bool) : ℕ → List Bool :=
  fun v => if v = cursorTape then w else s v

/-! ## §5 The two things the record ports cannot do, and the bank past the
envelope -/

/-! ## §6 THE DELIVERABLE: the all-`k` form of `Rounds`, without
`AddressDeterminacy` -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor
