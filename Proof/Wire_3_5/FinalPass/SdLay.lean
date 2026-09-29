import Proof.Wire_3_5.FinalPass.SdMask

/-! # S4 (the seeds phase), part 3: the per-seed body's layout and the carriers' mask factors in it (P3:3170-3178)

The per-seed body (the loops over centers and samples, the per-point step) runs on one word layout `BS` with
`bns = 46 + nw + nsc` streams and `bnr = 220 + nn + nrs` registers (`nw, nn, nsc, nrs` the SYM evaluator's counts):
- streams `0 … 29` fixed: `tN` (the numerator), `tC`, `tU`, `tV` (the point), `tSp` (`[true]`), three spare streams
  `tD0 … tD2`, the two tables `tT k`, per carrier `k < 2` its accumulators and scratch `tPos k`, `tNeg k`, `tX k`,
  `tZ k`, the THR evaluator's scratch `18 … 24`, the center counters `25, 26`;
- streams `30 + i`: the front's word `i` (`tG k` = word `2 + k`, the carrier's mask table; `tThr` = word `6`);
- streams `47 + nw + j`: the SYM evaluator's scratch;
- registers: `0` the evaluator's accumulator, `1 … 4` / `5 … 117` the THR evaluator's numbers / scratch, `rM k` the
  carriers' mask bits (`118 + k`), `rP k` their presence flags (`120 + k`), `122 …` the mask machine's registers,
  `154 …` the loops', `220 + i` the SYM evaluator's.

**`maskK k`**: `SdMask.maskOne` lifted onto carrier `k`'s streams (`fsM k`) and registers (`frM k`, bit into `rM k`).
**`maskK_spec`**: register `rM k` gains the carrier's factor `filterBits FP e (popBits true (cornerWord …))` of
`maskBits_point`, the corner word stays on `tX k`, the accumulators hold some binary values, nothing else moves.

Paper quantity of the main type: one carrier's factor of the mask `M(e,x)` at a sampled point, on the body's layout. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## Views -/

section View
variable {ns nr ns' nr' : ℕ}

/-- The state a renamed component sees. -/
def viewW (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr') : WState ns nr :=
  ⟨fun i => ω.sh (fs i), fun i => ω.st (fs i), fun q => ω.val (fr q), ω.cell⟩

theorem liftW_view (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') (ω : WState ns' nr') :
    LiftW fs fr ω (viewW fs fr ω) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

end View

/-! ## The layout -/

/-- The body's stream count. -/
def bns (nw nsc : ℕ) : ℕ := 46 + nw + nsc

/-- The body's register count. -/
def bnr (nn nrs : ℕ) : ℕ := 220 + nn + nrs

/-- The body's states and programs. -/
abbrev BS (nw nn nsc nrs : ℕ) := WState (bns nw nsc) (bnr nn nrs)
abbrev BP (nw nn nsc nrs : ℕ) := WM (bns nw nsc) (bnr nn nrs)

section Lay
variable {nw nn nsc nrs : ℕ}

/-- A fixed stream (below `47`). -/
def bst (i : ℕ) (h : i < 47) : Fin (bns nw nsc + 1) := ⟨i, by unfold bns; omega⟩

/-- A fixed register (below `220`). -/
def brg (i : ℕ) (h : i < 220) : Fin (bnr nn nrs) := ⟨i, by unfold bnr; omega⟩

def tN : Fin (bns nw nsc + 1) := bst 0 (by omega)
def tC : Fin (bns nw nsc + 1) := bst 1 (by omega)
def tU : Fin (bns nw nsc + 1) := bst 2 (by omega)
def tV : Fin (bns nw nsc + 1) := bst 3 (by omega)
def tSp : Fin (bns nw nsc + 1) := bst 4 (by omega)
def tD0 : Fin (bns nw nsc + 1) := bst 5 (by omega)
def tD1 : Fin (bns nw nsc + 1) := bst 6 (by omega)
def tD2 : Fin (bns nw nsc + 1) := bst 7 (by omega)
def tT (k : Fin 2) : Fin (bns nw nsc + 1) := bst (8 + k.val) (by omega)
def tPos (k : Fin 2) : Fin (bns nw nsc + 1) := bst (10 + 4 * k.val) (by omega)
def tNeg (k : Fin 2) : Fin (bns nw nsc + 1) := bst (11 + 4 * k.val) (by omega)
def tX (k : Fin 2) : Fin (bns nw nsc + 1) := bst (12 + 4 * k.val) (by omega)
def tZ (k : Fin 2) : Fin (bns nw nsc + 1) := bst (13 + 4 * k.val) (by omega)
/-- The front's word `i`. -/
def tW (i : Fin (17 + nw)) : Fin (bns nw nsc + 1) := ⟨30 + i.val, by unfold bns; omega⟩
/-- The carrier's mask table (word `2 + k`). -/
def tG (k : Fin 2) : Fin (bns nw nsc + 1) := bst (32 + k.val) (by omega)
/-- Stage 7's threshold (word `6`). -/
def tThr : Fin (bns nw nsc + 1) := bst 36 (by omega)

/-- The sampled pairs' word (word `1`): the only stream whose head moves between points. -/
def tI : Fin (bns nw nsc + 1) := bst 31 (by omega)

def rM (k : Fin 2) : Fin (bnr nn nrs) := brg (118 + k.val) (by omega)
def rP (k : Fin 2) : Fin (bnr nn nrs) := brg (120 + k.val) (by omega)

/-! ## Carrier `k`'s mask machine -/

/-- Carrier `k`'s streams for `maskOne` (the layout order: table, point, accumulators, corner word, population,
signs, the majority streams, the tables). -/
def fsMv (k : Fin 2) : Fin 14 → ℕ :=
  ![32 + k.val, 1, 2, 3, 10 + 4 * k.val, 11 + 4 * k.val, 12 + 4 * k.val, 13 + 4 * k.val, 4, 5, 36, 6, 8 + k.val, 7]

theorem fsMv_lt (k : Fin 2) (i : Fin 14) : fsMv k i < 47 := by
  have := k.isLt
  fin_cases i <;> simp [fsMv] <;> omega

theorem fsMv_inj (k : Fin 2) : Function.Injective (fsMv k) := by
  fin_cases k <;> decide

def fsM (k : Fin 2) (i : Fin 14) : Fin (bns nw nsc + 1) := bst (fsMv k i) (fsMv_lt k i)

theorem fsM_ne_tI (k : Fin 2) (i : Fin 14) : (fsM k i : Fin (bns nw nsc + 1)) ≠ tI := by
  intro h
  have e := congrArg Fin.val h
  simp only [fsM, tI, bst] at e
  have := k.isLt
  revert e
  fin_cases i <;> simp [fsMv] <;> omega

theorem fsM_inj (k : Fin 2) : Function.Injective (fsM (nw := nw) (nsc := nsc) k) := fun _ _ h =>
  fsMv_inj k (congrArg Fin.val h)

/-- Carrier `k`'s registers for `maskOne`: `26` (the bit) to `rM k`, the others to `122 + q`. -/
def frM (k : Fin 2) (q : Fin 32) : Fin (bnr nn nrs) :=
  brg (if q.val = 26 then 118 + k.val else 122 + q.val) (by have := k.isLt; have := q.isLt; split_ifs <;> omega)

theorem frM_inj (k : Fin 2) : Function.Injective (frM (nn := nn) (nrs := nrs) k) := by
  intro a b h
  have e := congrArg Fin.val h
  simp only [frM, brg] at e
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at e with h1 h2 h2 <;> omega

theorem frM_26 (k : Fin 2) : (frM k 26 : Fin (bnr nn nrs)) = rM k := Fin.ext (by simp [frM, rM, brg])

theorem frM_lo (k : Fin 2) (q : Fin 32) (hq : q.val ≠ 26) :
    (frM k q : Fin (bnr nn nrs)) = brg (122 + q.val) (by have := q.isLt; omega) :=
  Fin.ext (by simp [frM, brg, hq])

/-- **Carrier `k`'s mask factor into `rM k`.** -/
def maskK (k : Fin 2) : BP nw nn nsc nrs := maskOne.liftW (fsM k) (frM k)

theorem maskK_spec (cap : ℕ) (k : Fin 2) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n)
    (c u v : BitInput n) (A B : ℕ) (ys : List Bool) (ω : BS nw nn nsc nrs)
    (hG : ω.st (tG k) = gatesW (PrimT.tabH X) (maskGates X)) (hC : ω.st tC = frame (List.ofFn c))
    (hU : ω.st tU = frame (List.ofFn u)) (hV : ω.st tV = frame (List.ofFn v))
    (hpos : ω.st (tPos k) = frameP (binary (PrimT.tabH X) A) ++ [false])
    (hneg : ω.st (tNeg k) = frameP (binary (PrimT.tabH X) B) ++ [false]) (hX : ω.st (tX k) = ys ++ [false])
    (hys : ys.length = 8 * (maskGates X).length)
    (hZ : ω.st (tZ k) = List.replicate (2 * (maskGates X).length + 1) false) (hSp : ω.st tSp = [true])
    (hT : ω.st (tT k) = tableWord (filterTable FP e (maskGates X).length))
    (hH : ω.st tThr = ListEval.unary (majorityThreshold FP.walkLen))
    (hsh : ∀ i : Fin 14, ω.sh (fsM k i) = 0) (hms : ∀ (j : ℕ) (hj : j < 14), ω.val (brg (122 + j) (by omega)) = 0)
    (hcap : MkCap cap (PrimT.tabH X) n (maskGates X).length (filterTable FP e (maskGates X).length)
      (majorityThreshold FP.walkLen))
    (hM : ω.val (rM k) + 1 ≤ cap) :
    ∃ ω' A' B', WExec cap (maskK k) ω ω' (mkCost (PrimT.tabH X) n (maskGates X).length
        (tableWord (filterTable FP e (maskGates X).length)).length (majorityThreshold FP.walkLen)) ∧
      ω'.st (tX k) = frameP (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v) ++ [false] ∧
      ω'.st (tPos k) = frameP (binary (PrimT.tabH X) A') ++ [false] ∧
      ω'.st (tNeg k) = frameP (binary (PrimT.tabH X) B') ++ [false] ∧
      (∀ i, i ≠ tPos k → i ≠ tNeg k → i ≠ tX k → ω'.st i = ω.st i) ∧ ω'.sh = ω.sh ∧
      ω'.val = Function.update ω.val (rM k) (ω.val (rM k) +
        (filterBits FP e (popBits true (cornerWord ((maskGates X).map NormalizedThresholdGate.eval) c u v))).toNat) ∧
      ω'.cell = ω.cell := by
  have hv26 : (viewW (fsM k) (frM k) ω).val 26 = ω.val (rM k) := by
    show ω.val (frM k 26) = _
    rw [frM_26]
  obtain ⟨ω1, A', B', e1, x1, p1, n1, o1, h1, v1, k1⟩ := maskOne_carrier cap FP e X c u v A B ys
    (viewW (fsM k) (frM k) ω) hG hC hU hV hpos hneg hX hys hZ hSp hT hH hsh
    (fun q hq => by
      show ω.val (frM k q) = 0
      rw [frM_lo k q (by omega)]
      exact hms q.val hq)
    hcap (by rw [hv26]; exact hM)
  have e2 := ThrPt.WExec.liftW_upd cap (fsM_inj k) (frM_inj k) e1 ω (liftW_view _ _ ω)
  refine ⟨_, A', B', e2, ?_, ?_, ?_, fun i i1 i2 i3 => ?_, ?_, ?_, ?_⟩
  · show (ThrPt.updW (fsM k) (frM k) ω ω1).st (fsM k 6) = _
    rw [ThrPt.updW_st_in (fsM_inj k)]
    exact x1
  · show (ThrPt.updW (fsM k) (frM k) ω ω1).st (fsM k 4) = _
    rw [ThrPt.updW_st_in (fsM_inj k)]
    exact p1
  · show (ThrPt.updW (fsM k) (frM k) ω ω1).st (fsM k 5) = _
    rw [ThrPt.updW_st_in (fsM_inj k)]
    exact n1
  · by_cases hi : ∃ j, fsM k j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [ThrPt.updW_st_in (fsM_inj k)]
      have j4 : j ≠ sPos := fun h => i1 (by rw [h]; rfl)
      have j5 : j ≠ sNeg := fun h => i2 (by rw [h]; rfl)
      have j6 : j ≠ sX := fun h => i3 (by rw [h]; rfl)
      exact o1 j j4 j5 j6
    · exact ThrPt.updW_st_out _ _ i (fun j h => hi ⟨j, h⟩)
  · funext i
    by_cases hi : ∃ j, fsM k j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [ThrPt.updW_sh_in (fsM_inj k), congrFun h1 j]
      rfl
    · exact ThrPt.updW_sh_out _ _ i (fun j h => hi ⟨j, h⟩)
  · funext q
    by_cases hq : ∃ j, frM k j = q
    · obtain ⟨j, rfl⟩ := hq
      rw [ThrPt.updW_val_in (frM_inj k), v1]
      by_cases hj : j = 26
      · subst hj
        rw [Function.update_self, frM_26, Function.update_self, hv26]
      · have hne : (frM k j : Fin (bnr nn nrs)) ≠ rM k := fun h =>
          hj (frM_inj (nn := nn) (nrs := nrs) k (h.trans (frM_26 k).symm))
        rw [Function.update_of_ne hj, Function.update_of_ne hne]
        rfl
    · have hne : q ≠ rM k := fun h => hq ⟨26, by rw [h, frM_26]⟩
      rw [ThrPt.updW_val_out _ _ q (fun j h => hq ⟨j, h⟩), Function.update_of_ne hne]
  · rw [ThrPt.updW_cell]
    exact k1

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
