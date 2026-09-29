import Proof.CaseAnalysis.FinalPrinterBridge
import Proof.CaseAnalysis.RowsUniversalLowering
import Proof.MachineModel.NativeRowInput

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.ThresholdCompiler
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput

noncomputable section

/-! ## 1. The residual reindexer (H2) — the only new mathematics -/

section Hardwire
variable {q : ℕ}

/-- A.2's reassembly at general arity. Definitionally `C10PrinterBridge.inputOf` once
`live := normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale`. -/
def joinInput (live : Finset (Fin q)) (y : BitInput live.card) (z : BitInput liveᶜ.card) :
    BitInput q := (normalizedLiveExternalInputEquiv live).symm (y, z)

theorem joinInput_coord (live : Finset (Fin q)) (y : BitInput live.card) (z : BitInput liveᶜ.card)
    (c : Fin live.card ⊕ Fin liveᶜ.card) :
    joinInput live y z (normalizedLiveExternalCoordinateEquiv live c) = Sum.elim y z c := by
  unfold joinInput normalizedLiveExternalInputEquiv bitInputSumEquiv
  simp [Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- **The `q → q-K` hardwiring of one live assignment `y`** (paper.tex:2870). The live block's
partial score is subtracted from the exact target; the residual coordinates keep their weights. -/
def hardwire (live : Finset (Fin q)) (g : ExactThresholdGate q) (y : BitInput live.card) :
    ExactThresholdGate liveᶜ.card where
  weight := fun i => g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inr i))
  target := g.target -
    ∑ j : Fin live.card,
      g.weight (normalizedLiveExternalCoordinateEquiv live (Sum.inl j)) * (if y j then 1 else 0)

/-- The arity cast `liveᶜ.card = (s+1)/2 + s/2` demanded by `CloseoutRowsSharedInput.input`. -/
def castGate {m n : ℕ} (h : m = n) (g : ExactThresholdGate n) : ExactThresholdGate m where
  weight := fun i => g.weight (Fin.cast h i)
  target := g.target

/-- The pool coordinate a malformed occurrence code is sent to: never satisfied, matching
`encodedFiniteBooleanAssignment`'s "invalid codes are false". -/
def falseGate (n : ℕ) : ExactThresholdGate n := ⟨fun _ => 0, 1⟩

/-- The printer's matrix point `(i,j)` as a point of the residual cube: A.12's two half-cubes
(`RowBinLift.assignment`, `Proof/Supplier/RowBinLiftCuts.lean`). -/
def halfPoint (l r rowN colN : ℕ) : BitInput (l+r) :=
  fun k => Fin.addCases (fun i : Fin l => rowN.testBit i.val)
    (fun i : Fin r => colN.testBit i.val) k

end Hardwire

/-! ## 2. The pool: one gate per (pooled exact child, live assignment) -/

section Pool
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)

/-- The `2^K` live assignments, in the canonical `Fintype` order. -/
def liveList : List (BitInput live.card) := (Finset.univ : Finset (BitInput live.card)).toList

theorem liveList_length : (liveList live).length = 2 ^ live.card := by
  rw [liveList, Finset.length_toList, Finset.card_univ, card_bitInput]

/-- The pooled exact-child cache of A.2's `X`/`C` pool (S3a), at arity `q`. -/
def childList : List (ExactThresholdGate q) :=
  ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ)

/-- The arity-`q` never-satisfied gate, the `getD` default of `childList`. -/
def falseChild : ExactThresholdGate q := falseGate q

/-- `pool` entry number `k+1`: child `k % B` hardwired at live assignment `k / B`. -/
def poolFn (harity : (s+1)/2+s/2 = liveᶜ.card) (k : ℕ) :
    ExactThresholdGate ((s+1)/2+s/2) :=
  castGate harity (hardwire live
    ((childList a live occ).getD (k % (childList a live occ).length) (falseChild))
    ((liveList live).getD (k / (childList a live occ).length) (fun _ => false)))

/-- **The pool** (paper.tex:2870): the sentinel coordinate, then one exact-threshold coordinate over
the residual variables for every (pooled child, live assignment) pair. -/
def pool (harity : (s+1)/2+s/2 = liveᶜ.card) : List (ExactThresholdGate ((s+1)/2+s/2)) :=
  falseGate ((s+1)/2+s/2) ::
    List.ofFn (fun k : Fin ((liveList live).length * (childList a live occ).length) =>
      poolFn a live occ s harity k.val)

theorem pool_length (harity : (s+1)/2+s/2 = liveᶜ.card) :
    (pool a live occ s harity).length =
      (liveList live).length * (childList a live occ).length + 1 := by
  rw [pool, List.length_cons, List.length_ofFn]

/-- The residual point underlying a matrix coordinate of the printed table. -/
def residualPoint (harity : (s+1)/2+s/2 = liveᶜ.card) (x : BitInput ((s+1)/2+s/2)) :
    BitInput liveᶜ.card := fun i => x (Fin.cast harity.symm i)

/-- The pool index of occurrence-child code `c` at live assignment number `yi`. -/
def poolIndex (harity : (s+1)/2+s/2 = liveᶜ.card) (yi : Fin (liveList live).length) (c : ℕ) :
    Fin (pool a live occ s harity).length :=
  if h : c < (childList a live occ).length then
    ⟨(childList a live occ).length * yi.val + c + 1, by
      rw [pool_length]
      have h1 : (childList a live occ).length * (yi.val + 1) ≤
          (childList a live occ).length * (liveList live).length :=
        Nat.mul_le_mul_left _ yi.isLt
      rw [Nat.mul_succ] at h1
      have h2 : (liveList live).length * (childList a live occ).length =
          (childList a live occ).length * (liveList live).length := Nat.mul_comm _ _
      omega⟩
  else ⟨0, by rw [pool_length]; omega⟩

end Pool

/-! ## 3. The bank, its size gates, and `rowInput` -/

section Bank
variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)

/-- The monomials of one bank row, as pool indices: the S3a lowering of `P` with every occurrence
code sent to its coordinate at live assignment `yi`. -/
def indexRow (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial)
    (yi : Fin (liveList live).length) : List (List (Fin (pool a live occ s harity).length)) :=
  (CloseoutRowsUniversal.lower a live occ P).map
    (fun m => m.map (poolIndex a live occ s harity yi))

/-- The occurrence-index bank `ExtIncidence.NativeRowInput.input` consumes, one row per live
assignment (paper.tex:2870). -/
def ps (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    List (List (List (Fin (pool a live occ s harity).length))) :=
  List.ofFn (indexRow a live occ s harity P)

/-- **The bank**: `ExtIncidence.NativeRowInput.bank` turns the index lists into the monomial masks
`CloseoutRowsCacheInput.family` expects. -/
def bank (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    List (List (List Bool)) :=
  ExtIncidence.NativeRowInput.bank (ps a live occ s harity P)

/-- **`2^K` hardwired live assignments** — paper.tex:2870. -/
theorem bank_length (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    (bank a live occ s harity P).length = 2 ^ live.card := by
  rw [bank, ExtIncidence.NativeRowInput.bank, List.length_map, ps, List.length_ofFn,
    liveList_length]

/-- Every bank row has `N_mon` monomials, so `hw` of `NativeRowInput.input` is the lowering bound. -/
theorem ps_rows_lt (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w) :
    ∀ ms ∈ ps a live occ s harity P, ms.length < 2 ^ w := by
  intro ms hms
  obtain ⟨yi, rfl⟩ := List.mem_ofFn.mp hms
  simpa only [indexRow, List.length_map] using hmon

/-- `bank_rows_le` of P2R §1.5, free from `ExtIncidence.NativeRowInput.bank_width`. -/
theorem bank_rows_le (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w) :
    ∀ rows ∈ bank a live occ s harity P, rows.length ≤ 2 ^ w :=
  ExtIncidence.NativeRowInput.bank_width (ps a live occ s harity P) w
    (ps_rows_lt a live occ s harity P w hmon)

/-- Every bank row is a list of `pool`-length characteristic vectors — `rawRows` is `List.ofFn`. -/
theorem bank_row_length (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) :
    ∀ rows ∈ bank a live occ s harity P, ∀ row ∈ rows,
      row.length = (pool a live occ s harity).length := by
  intro rows hrows row hrow
  obtain ⟨ms, _, rfl⟩ := List.mem_map.mp hrows
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hrow
  exact List.length_ofFn

/-- The BinLift batch length `CloseoutRowsCacheInput.input` measures is the emitted cut count
`raw_cuts_gate` bounds (`CloseoutRowsSharedDigits.batch_perm` + `RowPowerBinLift.batch_length`). -/
theorem batch_length_eq {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (bk : List (List (List Bool))) (hw : ∀ rows ∈ bk, rows.length ≤ 2 ^ w) :
    (RowBinLift.batch Q (CloseoutRowsCacheInput.family gs bk)).length =
      (bk.flatMap (CloseoutRowsSharedDigits.cuts gs Q w)).length := by
  rw [(CloseoutRowsSharedDigits.batch_perm gs Q w bk hw).length_eq, RowPowerBinLift.batch_length]

/-- **The size gate** (`hg` of `NativeRowInput.input`), `Q := K+1` verbatim as in `raw_cuts_gate`. -/
theorem gate (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w) (hpos : 1 ≤ w)
    (hload : 200 * (live.card + w * (live.card + 2)) ≤ s) :
    (RowBinLift.batch (live.card + 1)
      (CloseoutRowsCacheInput.family (pool a live occ s harity)
        (bank a live occ s harity P))).length ^ 100 ≤ 2 ^ s := by
  have hw := bank_rows_le a live occ s harity P w hmon
  rw [batch_length_eq (pool a live occ s harity) (live.card + 1) w
    (bank a live occ s harity P) hw]
  exact CloseoutRawRows.raw_cuts_gate (pool a live occ s harity) live.card w s
    (bank a live occ s harity P) (le_of_eq (bank_length a live occ s harity P)) hw hpos hload

def rowInput (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s) : EquationRow.Input :=
  ExtIncidence.NativeRowInput.input s (live.card + 1) w (pool a live occ s harity)
    (ps a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (ps_rows_lt a live occ s harity P w hmon)

end Bank

/-! ## 4. `bank_eval` — the one semantic identity -/

section Eval

end Eval

/-! ## 5. The C10 instantiation consumed by S3c-2 / S4 / S1 -/

section C10

end C10


end

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput
