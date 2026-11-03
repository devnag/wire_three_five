import Proof.CaseAnalysis.FinalRowAnswerWord
import Proof.CaseAnalysis.FinalBandClearDock
import Proof.CaseAnalysis.FinalRoundCursor
import Proof.CaseAnalysis.FinalWordFunctionDock

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundBudget

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift
  (answerShiftFuel answerShiftFuel_eq)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord (rowAnswerFuel)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10BandClearDock (clear_budget)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor
  (unaryCursorCost unaryCursorCost_eq)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountCap
  (siteCap site_le length_flatMap_le scale_length)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
  (siteRecords callRecords siteCalls)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (addressRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage (Rounds)
open NearCubicWires.RepairSource.CloseoutFinal.C10LedgerBounds (countRecordAppend_le)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule)
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
  (polyFuel poly_polylog_le_polyFuel repinOnset)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel polyFuel_le_hotFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10WordFunctionDock
  (rewound inSlot clause_dock)
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

/-! ## §1  `q^{O(1)}` as a predicate

`paper.tex:1382-1385` and `paper.tex:4306-4308` are the two sentences that put a
budget in `ENDGAME_RESOURCE.md` §2's FREE/POLYLOG row, and both say the same
thing: a fixed power of `q`.  `widthPower sources k c N = (q(N)+1)^c`
(`Proof/CaseAnalysis/FinalPartsSchedule.lean`) is that shape already, so the
predicate is a constant times one of those.  It is closed under `+` and `*`,
which is the whole content of "a SUM of stages each `q^{O(1)}` is `q^{O(1)}`". -/

/-- **The paper's `q^{O(1)}` (`paper.tex:1382-1385`), as a predicate on budget
families.** -/
def WidthPoly (sources : RepairSource.EightSources) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ A c : ℕ, ∀ N, f N ≤ A * widthPower sources k c N

/-- A pointwise-smaller family is still `q^{O(1)}`. -/
theorem WidthPoly.mono {sources : RepairSource.EightSources} {k : ℕ} {f g : ℕ → ℕ}
    (h : ∀ N, g N ≤ f N) (hf : WidthPoly sources k f) : WidthPoly sources k g := by
  obtain ⟨A, c, hA⟩ := hf
  exact ⟨A, c, fun N => le_trans (h N) (hA N)⟩

/-- A constant is `q^{O(1)}` at exponent `0`. -/
theorem WidthPoly.const (sources : RepairSource.EightSources) (k a : ℕ) :
    WidthPoly sources k (fun _ => a) := by
  refine ⟨a, 0, fun N => ?_⟩
  unfold widthPower
  simp

/-- **Closure under `+` -- the lemma that makes a per-round SUM legal.**  The
exponents add rather than max, which costs nothing and avoids a case split. -/
theorem WidthPoly.add {sources : RepairSource.EightSources} {k : ℕ} {f g : ℕ → ℕ}
    (hf : WidthPoly sources k f) (hg : WidthPoly sources k g) :
    WidthPoly sources k (fun N => f N + g N) := by
  obtain ⟨A, c, hA⟩ := hf
  obtain ⟨B, d, hB⟩ := hg
  refine ⟨A + B, c + d, fun N => ?_⟩
  have hc : widthPower sources k c N ≤ widthPower sources k (c + d) N := by
    unfold widthPower
    exact Nat.pow_le_pow_right (by omega) (Nat.le_add_right c d)
  have hd : widthPower sources k d N ≤ widthPower sources k (c + d) N := by
    unfold widthPower
    exact Nat.pow_le_pow_right (by omega) (Nat.le_add_left d c)
  show f N + g N ≤ (A + B) * widthPower sources k (c + d) N
  calc f N + g N ≤ A * widthPower sources k c N + B * widthPower sources k d N :=
        Nat.add_le_add (hA N) (hB N)
    _ ≤ A * widthPower sources k (c + d) N + B * widthPower sources k (c + d) N :=
        Nat.add_le_add (Nat.mul_le_mul_left A hc) (Nat.mul_le_mul_left B hd)
    _ = (A + B) * widthPower sources k (c + d) N := by ring

/-- **Closure under `*`** -- one round runs `terms` copies of the per-monomial
work, and `terms` is itself `q^{O(1)}` (`addressRecords_length_le`). -/
theorem WidthPoly.mul {sources : RepairSource.EightSources} {k : ℕ} {f g : ℕ → ℕ}
    (hf : WidthPoly sources k f) (hg : WidthPoly sources k g) :
    WidthPoly sources k (fun N => f N * g N) := by
  obtain ⟨A, c, hA⟩ := hf
  obtain ⟨B, d, hB⟩ := hg
  refine ⟨A * B, c + d, fun N => ?_⟩
  have hsplit : widthPower sources k (c + d) N
      = widthPower sources k c N * widthPower sources k d N := by
    unfold widthPower
    rw [← pow_add]
  calc f N * g N ≤ A * widthPower sources k c N * (B * widthPower sources k d N) :=
        Nat.mul_le_mul (hA N) (hB N)
    _ = A * B * (widthPower sources k c N * widthPower sources k d N) := by ring
    _ = A * B * widthPower sources k (c + d) N := by rw [hsplit]

/-! ## §2  The record width, and the three compiled stage charges -/

/-- **Stage 2a, the summation half of the answer channel.**  `rowAnswerFuel w rows
= 2*(rows*(16*w+20)+5)+2` (`Proof/CaseAnalysis/FinalRowAnswerWord.lean`) is
bilinear in the record width and the external-row count. -/
theorem widthPoly_rowAnswerFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows : ℕ → ℕ} (hw : WidthPoly sources k w) (hrows : WidthPoly sources k rows) :
    WidthPoly sources k (fun N => rowAnswerFuel (w N) (rows N)) := by
  refine WidthPoly.mono (f := fun N => 32 * (rows N * w N) + (40 * rows N + 12))
    (fun N => le_of_eq (by unfold rowAnswerFuel; ring)) ?_
  exact ((WidthPoly.const sources k 32).mul (hrows.mul hw)).add
    (((WidthPoly.const sources k 40).mul hrows).add (WidthPoly.const sources k 12))

/-- **Stage 2b, the shift half of the answer channel.**  `answerShiftFuel_eq`
(`Proof/CaseAnalysis/FinalAnswerShift.lean`) is `128*(w+1)*(shift+2)`. -/
theorem widthPoly_answerShiftFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w shift : ℕ → ℕ} (hw : WidthPoly sources k w) (hshift : WidthPoly sources k shift) :
    WidthPoly sources k (fun N => answerShiftFuel (w N) (shift N)) := by
  refine WidthPoly.mono (f := fun N => 128 * ((w N + 1) * (shift N + 2)))
    (fun N => le_of_eq (by rw [answerShiftFuel_eq]; ring)) ?_
  exact (WidthPoly.const sources k 128).mul
    ((hw.add (WidthPoly.const sources k 1)).mul (hshift.add (WidthPoly.const sources k 2)))

theorem widthPoly_recordAppend (sources : RepairSource.EightSources) (k : ℕ)
    {w : ℕ → ℕ} (hw : WidthPoly sources k w) :
    WidthPoly sources k (fun N => CompetitorCountRecordAppend.budget (w N)) := by
  refine WidthPoly.mono (f := fun N => 25120 * ((w N + 1) * (w N + 1))) (fun N => ?_) ?_
  · have h := countRecordAppend_le (w N)
    have hsq : (w N + 1) ^ 2 = (w N + 1) * (w N + 1) := by ring
    omega
  · exact (WidthPoly.const sources k 25120).mul
      ((hw.add (WidthPoly.const sources k 1)).mul (hw.add (WidthPoly.const sources k 1)))

/-! ## §3  The composed per-round fuel -/

def termFuel (w rows shift : ℕ) : ℕ :=
  rowAnswerFuel w rows + 1 + answerShiftFuel w shift + 1
    + CompetitorCountRecordAppend.budget w

/-- **A docked segment, then the clear that puts its slots back to `[]`.**
`round_clear_seq` (`Proof/CaseAnalysis/FinalBandClearDock.lean`) delivers a
single `Step` at `cost + 1 + (2*total + 4)` with `total := cost + 1`, which
`clear_budget` (`:385`) computes as `3*cost + 7`.

Use `round_clear_seq`, NOT `zeroBand_round_then_clear`: `round_step_of_dock`'s
`hframe` freezes tape `81`, so the latter cannot produce the port change
`Rounds` needs. -/
def clearedFuel (f : ℕ) : ℕ := 3 * f + 7

/-- **THE WHOLE ROUND.**  Decode the clause address (cleared), run the `terms`
monomials that address emits (each cleared, because the slots are reused), bump
the round cursor (cleared) -- every join a `Step.seq` bridge step. -/
def roundFuel (w rows shift decode cursor terms : ℕ) : ℕ :=
  clearedFuel decode + 1 + terms * (clearedFuel (termFuel w rows shift) + 1) + 1
    + clearedFuel cursor

/-- The per-monomial charge is `q^{O(1)}`. -/
theorem widthPoly_termFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows shift : ℕ → ℕ} (hw : WidthPoly sources k w) (hrows : WidthPoly sources k rows)
    (hshift : WidthPoly sources k shift) :
    WidthPoly sources k (fun N => termFuel (w N) (rows N) (shift N)) := by
  refine WidthPoly.mono
    (f := fun N => rowAnswerFuel (w N) (rows N) + 1 + answerShiftFuel (w N) (shift N) + 1
      + CompetitorCountRecordAppend.budget (w N)) (fun N => le_of_eq rfl) ?_
  exact ((((widthPoly_rowAnswerFuel sources k hw hrows).add (WidthPoly.const sources k 1)).add
    (widthPoly_answerShiftFuel sources k hw hshift)).add (WidthPoly.const sources k 1)).add
    (widthPoly_recordAppend sources k hw)

/-- A cleared segment is `q^{O(1)}` whenever the segment is. -/
theorem widthPoly_clearedFuel (sources : RepairSource.EightSources) (k : ℕ) {f : ℕ → ℕ}
    (hf : WidthPoly sources k f) : WidthPoly sources k (fun N => clearedFuel (f N)) := by
  refine WidthPoly.mono (f := fun N => 3 * f N + 7) (fun N => le_of_eq rfl) ?_
  exact ((WidthPoly.const sources k 3).mul hf).add (WidthPoly.const sources k 7)

/-- **The whole round -- every stage and every clear -- is `q^{O(1)}`.** -/
theorem widthPoly_roundFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows shift decode cursor terms : ℕ → ℕ} (hw : WidthPoly sources k w)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hcursor : WidthPoly sources k cursor)
    (hterms : WidthPoly sources k terms) :
    WidthPoly sources k
      (fun N => roundFuel (w N) (rows N) (shift N) (decode N) (cursor N) (terms N)) := by
  refine WidthPoly.mono
    (f := fun N => clearedFuel (decode N) + 1
      + terms N * (clearedFuel (termFuel (w N) (rows N) (shift N)) + 1) + 1
      + clearedFuel (cursor N)) (fun N => le_of_eq rfl) ?_
  exact ((((widthPoly_clearedFuel sources k hdecode).add (WidthPoly.const sources k 1)).add
    (hterms.mul ((widthPoly_clearedFuel sources k
      (widthPoly_termFuel sources k hw hrows hshift)).add
      (WidthPoly.const sources k 1)))).add (WidthPoly.const sources k 1)).add
    (widthPoly_clearedFuel sources k hcursor)

/-! ## §4  THE DELIVERABLE -- the per-round TOTAL under the paper's cell -/

/-! ## §5  `k`-FREENESS -- the check that decides whether this is one factor or two -/


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundBudget
