import Proof.Wire_3_5.Primitive.Writers.HashPops2
import Proof.Wire_3_5.FinalPass.ThrLoop

/-! # HASH setup (C), P2a part 3: a segment, a digit's two records, all digits, the erasure

* `elemCW`, **`elem_spec`**; `segLoopW`, **`segLoop_spec`**; `segCW`, **`seg_spec`** (`segW gis = gis.flatMap elemW ++
  [false]` copied);
* `digCW`, **`dig_spec`**: `popRec (false, gis) ++ popRec (true, gis)` appended (the segment copied twice behind the
  headers `[1, 0]`, `[1, 1]`), its length added to `DL`;
* `fmtW`, **`fmt_spec`**: every digit of the digit word `(ls).flatMap segW` (C1's `digsWord`), counted from `τ₀` in
  `R 3`;
* `eraseW`, **`erase_spec`**: the digit word's cells blanked back to the stream's start.

Paper quantity of the main type: the records `popRec (±, gis)` of a row's digit populations (P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.HbM (elemW popRec)

/-- A digit population's segment. -/
def segW (gis : List ℕ) : List Bool := gis.flatMap elemW ++ [false]

theorem elemW_eq (g : ℕ) : elemW g = List.replicate (g + 1) true ++ [false] := by
  simp [elemW, List.replicate_succ]

theorem elemW_len (g : ℕ) : (elemW g).length = g + 2 := by simp [elemW]

theorem wr_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons a l ih => simpa [writeTapeBit] using ih

/-- `u` copied from `Dg` to `O`: appended to the output, the digit stream's head and `K` advanced by `|u|`. -/
def LS.cp (t : LS) (u : List Bool) : LS := { t with out := t.out ++ u, dh := t.dh + u.length, k := t.k + u.length }

theorem rd_app0 (A B : List Bool) : readTapeBit (A ++ B) A.length = readTapeBit B 0 := by
  have e := rd_app A B 0
  rwa [Nat.add_zero] at e

section Seg
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

/-- An element `1^{g+1} 0`, copied. -/
def elemCW : WM ns nr := .seq (onesCW L) (cpBit L false)

theorem elem_spec (g : ℕ) (t : LS) (hb : ∀ i < g + 1, readTapeBit t.dg (t.dh + i) = true)
    (hz : readTapeBit t.dg (t.dh + (g + 1)) = false) (hc1 : t.out.length + (g + 2) ≤ cap)
    (hc2 : t.k + (g + 2) ≤ cap) :
    WExec cap (elemCW L) (t.w L σB)
      ((t.cp (elemW g)).w L σB) (15 * (g + 2)) := by
  have e1 := ones_spec cap L h σB (g + 1) t hb hz (by omega) (by omega)
  have e2 := cpBit_spec cap L h σB false
    { t with out := t.out ++ List.replicate (g + 1) true, dh := t.dh + (g + 1), k := t.k + (g + 1) }
    (by simp; omega) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  congr 1
  cases t
  simp only [LS.cp, LS.mk.injEq, List.append_assoc, elemW_eq, List.length_append, List.length_replicate,
    List.length_singleton, true_and, and_true]
  omega

/-- The elements of a segment, copied (until the segment's closing `0`). -/
def segLoopW : WM ns nr := .whs L.Dg (elemCW L)

theorem segLoop_spec (rest : List Bool) : ∀ (gis : List ℕ) (pre : List Bool) (t : LS),
    t.dg = pre ++ (gis.flatMap elemW ++ false :: rest) → t.dh = pre.length →
    t.out.length + (gis.flatMap elemW).length ≤ cap → t.k + (gis.flatMap elemW).length ≤ cap →
    WExec cap (segLoopW L) (t.w L σB)
      ((t.cp (gis.flatMap elemW)).w L σB) (17 * (gis.flatMap elemW).length + 1)
  | [], pre, t, hd, hh, _, _ => by
    have e := WExec.whsF (cap := cap) (P := elemCW L) (i := L.Dg) (σ := t.w L σB) (by
      unfold wbit; rw [w_st_Dg L h, w_sh_Dg L h, hd, hh]
      have := rd_app pre (false :: rest) 0
      simp only [List.flatMap_nil, List.nil_append, Nat.add_zero] at this ⊢
      rw [this]; rfl)
    have ht : t.cp (([] : List ℕ).flatMap elemW) = t := by cases t; simp [LS.cp]
    rw [ht]
    exact WExec.cast cap e rfl (by omega)
  | g :: gis, pre, t, hd, hh, hc1, hc2 => by
    have hflat : (g :: gis).flatMap elemW = elemW g ++ gis.flatMap elemW := by simp
    have hlen : ((g :: gis).flatMap elemW).length = (g + 2) + (gis.flatMap elemW).length := by
      rw [hflat, List.length_append, elemW_len]
    have hdg : t.dg = pre ++ (List.replicate (g + 1) true ++ (false :: (gis.flatMap elemW ++ false :: rest))) := by
      rw [hd, hflat, elemW_eq]; simp
    have e1 := elem_spec cap L h σB g t
      (fun i hi => by rw [hdg, hh, rd_app]; exact rd_ones (g + 1) i _ hi)
      (by rw [hdg, hh, rd_app]; exact rd_zero (g + 1) _) (by omega) (by omega)
    have ih := segLoop_spec rest gis (pre ++ elemW g) (t.cp (elemW g))
      (by simp only [LS.cp]; rw [hd, hflat]; simp) (by simp only [LS.cp]; rw [hh, List.length_append, elemW_len])
      (by simp only [LS.cp, List.length_append, elemW_len]; omega) (by simp only [LS.cp, elemW_len]; omega)
    have e := WExec.whsT (cap := cap) (i := L.Dg)
      (by unfold wbit; rw [w_st_Dg L h, w_sh_Dg L h, hdg, hh, rd_app0]; exact rd_ones (g + 1) 0 _ (by omega)) e1 ih
    refine WExec.cast cap e ?_ (by rw [hlen]; omega)
    congr 1
    cases t
    simp only [LS.cp, LS.mk.injEq, hflat, List.append_assoc, List.length_append, elemW_len, true_and, and_true]
    omega

/-- **A segment, copied**: its elements, then its closing `0`. -/
def segCW : WM ns nr := .seq (segLoopW L) (cpBit L false)

theorem seg_spec (gis : List ℕ) (pre rest : List Bool) (t : LS) (hd : t.dg = pre ++ (segW gis ++ rest))
    (hh : t.dh = pre.length) (hc1 : t.out.length + (segW gis).length ≤ cap) (hc2 : t.k + (segW gis).length ≤ cap) :
    WExec cap (segCW L) (t.w L σB)
      ((t.cp (segW gis)).w L σB) (17 * (segW gis).length + 15) := by
  have hs : (segW gis).length = (gis.flatMap elemW).length + 1 := by simp [segW]
  have e1 := segLoop_spec cap L h σB rest gis pre t (by rw [hd]; simp [segW]) hh (by omega) (by omega)
  have e2 := cpBit_spec cap L h σB false (t.cp (gis.flatMap elemW))
    (by simp only [LS.cp, List.length_append]; omega) (by simp only [LS.cp]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  congr 1
  cases t
  simp only [LS.cp, LS.mk.injEq, segW, List.append_assoc, List.length_append, List.length_singleton, true_and,
    and_true]
  omega

end Seg

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
