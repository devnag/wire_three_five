import Proof.Wire_3_5.FinalPass.DigsNav1

/-! # `DigsW`'s body, part 3: skipping to the selected child (P3:2543-2551)

Children before the selected one (`g_i` of them, each `|supp| + 1` integers) are skipped: `prodW` sets
`R 19 := g_i · (S + 1)` (clearing `R 18`), and `skipsW` steps over that many `intWord`s (`skip2W`). `navW` = header,
product, skips: the head ends at the selected child's first weight. Main declarations: `fm_split`, `prod_spec`,
`skips_spec`, **`nav_spec`**. Paper quantity: the selected child `child_i = children_i[g_i]` of `L_g`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

theorem fm_split (zs : List ℤ) (k : ℕ) : zs.flatMap intWord = (zs.take k).flatMap intWord ++ (zs.drop k).flatMap intWord := by
  rw [← List.flatMap_append, List.take_append_drop]

theorem fm_drop (zs : List ℤ) (k : ℕ) (h : k < zs.length) :
    (zs.drop k).flatMap intWord = intWord zs[k] ++ (zs.drop (k + 1)).flatMap intWord := by
  rw [List.drop_eq_getElem_cons h, List.flatMap_cons]

theorem fm_take (zs : List ℤ) (k : ℕ) (h : k < zs.length) :
    ((zs.take (k + 1)).flatMap intWord).length = ((zs.take k).flatMap intWord).length + (intWord zs[k]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- `R 19 += S + 1` (`S` in `R 15`). -/
def prodBodyW : WM ns nr := .seq (Hash4.wcopyR (R 15) (R 39) (R 40)) (.seq (WM.move (R 39) (R 19)) (.inc (R 19)))

/-- `R 19 := R 18 · (S + 1)`, `R 18` counted down. -/
def prodW : WM ns nr := countW (R 18) (prodBodyW R)

theorem prod_spec (n S : ℕ) (τ : WState ns nr) (h18 : τ.val (R 18) = n) (h19 : τ.val (R 19) = 0)
    (h15 : τ.val (R 15) = S) (h39 : τ.val (R 39) = 0) (h40 : τ.val (R 40) = 0) (hc : n * (S + 1) ≤ cap)
    (hn : n ≤ cap) (hS : S + 1 ≤ cap) :
    WExec cap (prodW R) τ ((τ.setv (R 18) 0).setv (R 19) (n * (S + 1))) (n * (25 * S + 13) + 1) := by
  have hF := count_spec cap (R 18) (prodBodyW R) n (25 * S + 9) hn
    (fun k => (τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))) (fun k _ => by simp)
    (fun k hk => by
      have hk1 : (k + 1) * (S + 1) = k * (S + 1) + S + 1 := by ring
      have hkc : k * (S + 1) + S + 1 ≤ cap := by
        rw [← hk1]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hc
      have d1 := Hash4.wcopyR_spec cap (R 15) (R 39) (R 40) (R.injective.ne (by decide)) (R.injective.ne (by decide))
        (R.injective.ne (by decide)) (((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1))
        (by simp [h39]) (by simp [h40]) (by simp [h15]; omega)
      have d2 := wmove_spec cap (R 39) (R 19) (R.injective.ne (by decide)) S
        ((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).setv (R 39)
          ((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).val (R 15)))
        (by simp [h15]) (by simp [h15]; omega) (by simp [h15]; omega)
      have d3 := WExec.inc (cap := cap) (R 19)
        (((((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).setv (R 39)
          ((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).val (R 15))).setv (R 39) 0).setv
          (R 19) (((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).setv (R 39)
          ((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).val (R 15))).val (R 19) +
          ((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).setv (R 39)
          ((((τ.setv (R 18) (n - k)).setv (R 19) (k * (S + 1))).setv (R 18) (n - k - 1)).val (R 15))).val (R 39))))
        (by simp [h15]; omega)
      refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by simp [h15]; omega)
      rw [hk1, show n - (k + 1) = n - k - 1 by omega]
      clear d1 d2 d3
      wst_eq)
  have e0 : (τ.setv (R 18) (n - 0)).setv (R 19) (0 * (S + 1)) = τ := by
    rw [Nat.sub_zero, Nat.zero_mul]; wst_eq
  rw [e0, Nat.sub_self] at hF
  exact WExec.mono hF (by rw [show 25 * S + 9 + 4 = 25 * S + 13 by ring])

/-- Step over `R 19` integers. -/
def skipsW (E : Fin (ns + 1)) : WM ns nr := countW (R 19) (skip2W E (R 14) (Rg R))

theorem skips_spec (E : Fin (ns + 1)) (zs : List ℤ) (Lm : ℕ) (hLm : ∀ z ∈ zs, natBitLength z.natAbs ≤ Lm)
    (c rest : List Bool) (j0 : ℕ) (τ : WState ns nr) (hst : τ.st E = frame c) (hs : τ.sh E = 2 * j0 + 1)
    (hp : τ.val (R 14) = j0) (hd : c.drop j0 = zs.flatMap intWord ++ rest) (h19 : τ.val (R 19) = zs.length)
    (h7 : τ.val (R 7) = 0) (hjc : j0 + (zs.flatMap intWord).length ≤ cap) (hn : zs.length ≤ cap) :
    WExec cap (skipsW R E) τ (at2 (τ.setv (R 19) 0) E (R 14) (j0 + (zs.flatMap intWord).length))
      (zs.length * (24 * Lm + 23) + 1) := by
  have hPc := Rg_ne_Pc R
  have hF := count_spec cap (R 19) (skip2W E (R 14) (Rg R)) zs.length (24 * Lm + 19) hn
    (fun k => at2 (τ.setv (R 19) (zs.length - k)) E (R 14) (j0 + ((zs.take k).flatMap intWord).length))
    (fun k _ => by simp [at2])
    (fun k hk => by
      have hsplit := fm_split zs k
      have hdk := fm_drop zs k hk
      have htk := fm_take zs k hk
      have hlen : ((zs.take k).flatMap intWord).length + (intWord zs[k]).length ≤ (zs.flatMap intWord).length := by
        rw [hsplit, hdk]; simp
      have d := skip2_spec cap E (R 14) (Rg R) hPc zs[k] c ((zs.drop (k + 1)).flatMap intWord ++ rest)
        (j0 + ((zs.take k).flatMap intWord).length)
        ((at2 (τ.setv (R 19) (zs.length - k)) E (R 14) (j0 + ((zs.take k).flatMap intWord).length)).setv (R 19)
          (zs.length - k - 1)) (by simp [at2, hst]) (by simp [at2]) (by simp [at2])
        (by rw [← List.drop_drop, hd, hsplit, List.append_assoc, List.drop_left, hdk, List.append_assoc])
        (by simp [at2, h7]) (by omega)
      refine WExec.cast cap d ?_ (by have := hLm zs[k] (List.getElem_mem hk); omega)
      rw [show zs.length - (k + 1) = zs.length - k - 1 by omega, htk, ← Nat.add_assoc]
      clear d hsplit hdk htk hlen
      wst_eq)
  have e0 : at2 (τ.setv (R 19) (zs.length - 0)) E (R 14) (j0 + ((zs.take 0).flatMap intWord).length) = τ := by
    rw [Nat.sub_zero, ← h19]; simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
    rw [ThrRead.setv_eq_self τ (R 19) _ rfl]; exact at2_self τ E (R 14) j0 hs hp
  rw [e0, Nat.sub_self, List.take_length] at hF
  exact WExec.mono hF (by ring_nf; omega)

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
