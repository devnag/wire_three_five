import Proof.Wire_3_5.Primitive.Writers.HashPops3

/-! # HASH setup (C), P2a part 4: a digit's two records, all digits, the erasure

* `digCW`, **`dig_spec`**: `popRec (false, gis) ++ popRec (true, gis)` appended (the segment copied twice behind the
  headers `[1, 0]`, `[1, 1]`), its length added to `DL`;
* `recsOf`; `fmtW`, **`fmt_spec`**: every digit of the digit word `ls.flatMap segW` (C1's `digsWord`), the count `τ₀`
  copied from `R 3`;
* `eraseW`, **`erase_spec`**: the digit word's cells blanked back to the stream's start.

Paper quantity of the main type: the records `popRec (±, gis)` of a row's digit populations (P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.HbM (elemW popRec)

/-- A digit's two population records. -/
def recsOf (gis : List ℕ) : List Bool := popRec (false, gis) ++ popRec (true, gis)

theorem recsOf_eq (gis : List ℕ) : recsOf gis = [true, false] ++ segW gis ++ ([true, true] ++ segW gis) := by
  simp [recsOf, popRec, segW]

theorem flat_take_succ {α : Type} (f : α → List Bool) (ls : List α) (k : ℕ) (hk : k < ls.length) :
    (ls.take (k + 1)).flatMap f = (ls.take k).flatMap f ++ f ls[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem flat_split {α : Type} (f : α → List Bool) (ls : List α) (k : ℕ) (hk : k < ls.length) :
    ls.flatMap f = (ls.take k).flatMap f ++ (f ls[k] ++ (ls.drop (k + 1)).flatMap f) := by
  rw [← List.append_assoc, ← flat_take_succ f ls k hk, ← List.flatMap_append, List.take_append_drop]

theorem flat_take_le {α : Type} (f : α → List Bool) (ls : List α) (k : ℕ) :
    ((ls.take k).flatMap f).length ≤ (ls.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop k ls]
  rw [List.flatMap_append, List.length_append]
  omega

theorem erase_dg (dg : List Bool) (m : ℕ) (hm : m < dg.length) :
    List.replicate m false ++ (dg.take m ++ false :: dg.drop (m + 1)).drop m = List.replicate (m + 1) false ++ dg.drop (m + 1) := by
  rw [List.drop_left' (by simp; omega), List.replicate_succ', List.append_assoc]
  rfl

section Dig
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

/-- **A digit's two records**: `[1, 0]`, the segment, rewind, `[1, 1]`, the segment again, its length into `DL`. -/
def digCW : WM ns nr :=
  .seq (Emit.emitW L.O L.OP [true, false]) (.seq (segCW L) (.seq (WM.rewind L.Dg L.K)
    (.seq (Emit.emitW L.O L.OP [true, true]) (.seq (segCW L) (WM.move L.K L.DL)))))

theorem dig_spec (gis : List ℕ) (pre rest : List Bool) (t : LS) (hd : t.dg = pre ++ (segW gis ++ rest))
    (hh : t.dh = pre.length) (hk : t.k = 0) (hc1 : t.out.length + 2 * (segW gis).length + 4 ≤ cap)
    (hc2 : t.dl + (segW gis).length ≤ cap) :
    WExec cap (digCW L) (t.w L σB)
      ({ t with out := t.out ++ recsOf gis, dh := pre.length + (segW gis).length, dl := t.dl + (segW gis).length }.w
        L σB) (46 * (segW gis).length + 69) := by
  have l2 : ∀ a b : Bool, [a, b].length = 2 := fun _ _ => rfl
  have s1 := Emit.emitW_spec cap L.O L.OP [true, false] (t.w L σB) (by rw [w_sh_O L h, w_st_O L h])
    (by rw [w_OP L h]; simp [l2]; omega)
  rw [appendO_w L h] at s1
  set t1 : LS := { t with out := t.out ++ [true, false] } with ht1
  have s2 := seg_spec cap L h σB gis pre rest t1 hd hh (by simp [ht1]; omega) (by simp [ht1, hk]; omega)
  have s3 := wrewind_spec cap L.Dg L.K (segW gis).length ((t1.cp (segW gis)).w L σB) (by rw [w_K L h]; simp [LS.cp, ht1, hk])
    (by rw [w_K L h]; simp [LS.cp, ht1, hk]; omega)
  rw [w_sh_Dg L h, setv_K_w L h, seth_Dg_w L h] at s3
  set t2 : LS := { t1.cp (segW gis) with k := 0, dh := (t1.cp (segW gis)).dh - (segW gis).length } with ht2
  have s4 := Emit.emitW_spec cap L.O L.OP [true, true] (t2.w L σB) (by rw [w_sh_O L h, w_st_O L h])
    (by rw [w_OP L h]; simp [l2, ht2, ht1, LS.cp]; omega)
  rw [appendO_w L h] at s4
  set t3 : LS := { t2 with out := t2.out ++ [true, true] } with ht3
  have s5 := seg_spec cap L h σB gis pre rest t3 (by simp [ht3, ht2, ht1, LS.cp, hd])
    (by simp [ht3, ht2, ht1, LS.cp, hh]) (by simp [l2, ht3, ht2, ht1, LS.cp]; omega) (by simp [ht3, ht2]; omega)
  have s6 := wmove_spec cap L.K L.DL (neK_DL L h) (segW gis).length ((t3.cp (segW gis)).w L σB) (by rw [w_K L h]; simp [LS.cp, ht3, ht2])
    (by rw [w_K L h]; simp [l2, LS.cp, ht3, ht2]; omega)
    (by rw [w_K L h, w_DL L h]; simp [l2, LS.cp, ht3, ht2, ht1]; omega)
  rw [setv_K_w L h, w_DL L h, w_K L h, setv_DL_w L h] at s6
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_
    (by simp only [l2]; omega)
  congr 1
  apply LS.ext <;> simp [l2, ht3, ht2, ht1, LS.cp, recsOf_eq, hk, hh] <;> omega

/-- **All digits**: the count `τ₀` from `R 3` into `DC`, then one digit per count. -/
def fmtW : WM ns nr := .seq (FinalPass.Hash4.wcopyR (L.R 3) L.DC L.T) (FinalPass.ThrArith.countW L.DC (digCW L))

theorem fmt_spec (ls : List (List ℕ)) (rest : List Bool) (t : LS) (hd : t.dg = ls.flatMap segW ++ rest)
    (hh : t.dh = 0) (hk : t.k = 0) (hdc : t.dc = 0) (hT : σB.val L.T = 0) (h3 : σB.val (L.R 3) = ls.length)
    (hn : ls.length ≤ cap)
    (hc1 : t.out.length + (ls.flatMap recsOf).length + 2 * (ls.flatMap segW).length + 4 ≤ cap)
    (hc2 : t.dl + (ls.flatMap segW).length ≤ cap) :
    WExec cap (fmtW L) (t.w L σB)
      ({ t with
          out := t.out ++ ls.flatMap recsOf
          dh := (ls.flatMap segW).length
          dl := t.dl + (ls.flatMap segW).length }.w L σB)
      (18 * ls.length + 3 + 1 + (ls.length * (46 * (ls.flatMap segW).length + 69 + 4) + 1)) := by
  have r3 : (t.w L σB).val (L.R 3) = ls.length := by
    rw [w_val_other L h σB t (L.R 3) (h.rOut 3 (by decide) (by decide) 0) (h.rOut 3 (by decide) (by decide) 1)
      (h.rOut 3 (by decide) (by decide) 2) (h.rOut 3 (by decide) (by decide) 3)
      (h.rOut 3 (by decide) (by decide) 4) (h.rOut 3 (by decide) (by decide) 5)
      (h.rOut 3 (by decide) (by decide) 6) (h.rOut 3 (by decide) (by decide) 7)]
    exact h3
  have c1 := FinalPass.Hash4.wcopyR_spec cap (L.R 3) L.DC L.T (h.rOut 3 (by decide) (by decide) 3)
    (h.rOut 3 (by decide) (by decide) 8) (neT_DC L h).symm (t.w L σB) (by rw [w_DC L h, hdc]) (by rw [w_T L h, hT])
    (by rw [r3]; exact hn)
  rw [r3, setv_DC_w L h] at c1
  set n := ls.length with hnd
  set F : ℕ → WState ns nr := fun k => ({ t with
      out := t.out ++ (ls.take k).flatMap recsOf
      dh := ((ls.take k).flatMap segW).length
      dl := t.dl + ((ls.take k).flatMap segW).length
      dc := n - k }).w L σB with hF
  have hF0 : F 0 = ({ t with dc := n }).w L σB := by
    simp only [hF, List.take_zero, List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero, Nat.sub_zero]
    congr 1
    apply LS.ext <;> simp [hh]
  have hFn : F n = ({ t with
      out := t.out ++ ls.flatMap recsOf
      dh := (ls.flatMap segW).length
      dl := t.dl + (ls.flatMap segW).length }).w L σB := by
    simp only [hF, hnd, List.take_length, Nat.sub_self]
    congr 1
    apply LS.ext <;> simp [hdc]
  have loop := FinalPass.ThrArith.count_spec cap L.DC (digCW L) n (46 * (ls.flatMap segW).length + 69) hn F
    (fun k _ => by simp only [hF]; rw [w_DC L h])
    (fun k hkn => by
      simp only [hF]
      rw [setv_DC_w L h]
      have hk' : k < ls.length := hkn
      have e := dig_spec cap L h σB ls[k] ((ls.take k).flatMap segW) ((ls.drop (k + 1)).flatMap segW ++ rest)
        ({ t with
            out := t.out ++ (ls.take k).flatMap recsOf
            dh := ((ls.take k).flatMap segW).length
            dl := t.dl + ((ls.take k).flatMap segW).length
            dc := n - k - 1 })
        (by simp only; rw [hd, flat_split segW ls k hk']; simp)
        rfl (by simp only; exact hk)
        (by
          simp only [List.length_append]
          have a1 := flat_take_le recsOf ls k
          have a2 := flat_take_le segW ls (k + 1)
          rw [flat_take_succ segW ls k hk', List.length_append] at a2
          have a3 : (recsOf ls[k]).length = 2 * (segW ls[k]).length + 4 := by
            rw [recsOf_eq]; simp; omega
          have a4 := flat_take_le recsOf ls (k + 1)
          rw [flat_take_succ recsOf ls k hk', List.length_append] at a4
          omega)
        (by
          simp only
          have a2 := flat_take_le segW ls (k + 1)
          rw [flat_take_succ segW ls k hk', List.length_append] at a2
          omega)
      refine WExec.cast cap e ?_ (by
        have a2 := flat_take_le segW ls (k + 1)
        rw [flat_take_succ segW ls k hk', List.length_append] at a2
        omega)
      congr 1
      apply LS.ext <;> simp [flat_take_succ recsOf ls k hk', flat_take_succ segW ls k hk'] <;> omega)
  rw [hF0, hFn] at loop
  exact WExec.seq c1 loop

/-- **The erasure**: `DL` cells blanked backwards from the head. -/
def eraseW : WM ns nr := .whr L.DL (.seq (.dec L.DL) (.seq (.bwd L.Dg) (.wr L.Dg false)))

theorem erase_spec : ∀ (m : ℕ) (t : LS), t.dl = m → t.dh = m → m ≤ t.dg.length → m ≤ cap →
    WExec cap (eraseW L) (t.w L σB)
      ({ t with dg := List.replicate m false ++ t.dg.drop m, dh := 0, dl := 0 }.w L σB) (7 * m + 1)
  | 0, t, hl, hh, _, _ => by
    have e := WExec.whrF (cap := cap) (P := .seq (.dec L.DL) (.seq (.bwd L.Dg) (.wr L.Dg false))) (r := L.DL)
      (σ := t.w L σB) (by rw [w_DL L h, hl])
    refine WExec.cast cap e ?_ le_rfl
    congr 1
    apply LS.ext <;> simp [hl, hh]
  | m + 1, t, hl, hh, hlen, hc => by
    have d1 := WExec.dec (cap := cap) L.DL (t.w L σB) (by rw [w_DL L h, hl]; exact hc)
    rw [w_DL L h, hl, setv_DL_w L h] at d1
    have d2 := WExec.bwd (cap := cap) L.Dg ({ t with dl := m + 1 - 1 }.w L σB)
    rw [w_sh_Dg L h, seth_Dg_w L h] at d2
    have d3 := WExec.wr (cap := cap) L.Dg false ({ t with dl := m + 1 - 1, dh := t.dh - 1 }.w L σB)
    rw [w_st_Dg L h, w_sh_Dg L h, sets_Dg_w L h] at d3
    have hm : m < t.dg.length := by omega
    have hsplit : t.dg = t.dg.take m ++ t.dg[m] :: t.dg.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hw : writeTapeBit t.dg (t.dh - 1) false = t.dg.take m ++ false :: t.dg.drop (m + 1) := by
      rw [hh, show m + 1 - 1 = m by omega]
      conv_lhs => rw [hsplit]
      have := wr_mid (t.dg.take m) (t.dg.drop (m + 1)) t.dg[m] false
      rwa [List.length_take, Nat.min_eq_left (by omega)] at this
    rw [hw] at d3
    have ih := erase_spec m
      { t with dl := m + 1 - 1, dh := t.dh - 1, dg := t.dg.take m ++ false :: t.dg.drop (m + 1) }
      (by simp) (by simp [hh]) (by simp; omega) (by omega)
    have e := WExec.whrT (cap := cap) (r := L.DL) (by rw [w_DL L h, hl]; omega) (WExec.seq d1 (WExec.seq d2 d3)) ih
    refine WExec.cast cap e ?_ (by omega)
    congr 1
    apply LS.ext
    · rfl
    · exact erase_dg t.dg m hm
    all_goals simp

end Dig

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
