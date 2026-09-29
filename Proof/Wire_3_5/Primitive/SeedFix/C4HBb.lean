import Proof.Wire_3_5.Primitive.SeedFix.C4HBa

/-! # C4HB, part 2: the printed words below the data size

P3:2262-2268 (the Hb printer's term words). With `s = hbS D` and `Q = s + 1`: a cell's term word is at most
`1100·Q³` long (its coefficient word, the HASH factor's polynomial, the `2t` factor records of `zRec`), and the
output before cell `c ≤ n` at most `1100·Q⁴`.

* `polyWord_le_ht`, `monoRoom_le`, `tb_le`, `cellWord_le`, **`outAt_le`**.

Paper quantity: none (the Hb printer's sizes). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)

theorem polyWord_le_ht (Fs : List (List (List ℕ))) (idx : ℕ) :
    (polyWord (Fs.getD idx [])).length ≤ (htWord Fs).length := by
  by_cases h : idx < Fs.length
  · rw [List.getD_eq_getElem _ _ h, ht_split Fs idx h]
    simp only [List.length_append, SeedFix.entryRec, SeedFix.rowRec, ListMachine.Rec.exprWord,
      ListMachine.Rec.termWord, List.flatMap_cons, List.flatMap_nil, List.length_cons, List.append_nil]
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    rw [htWord_eq]
    simp [polyWord]

theorem monoRoom_le (q4 G s : ℕ) (hq : q4 ≤ 4 * s) (hG : G ≤ s) : monoRoom q4 G G ≤ 106 * (s + 1) ^ 2 := by
  unfold monoRoom atomRoom
  have h1 : (q4 + 3) * G ≤ (4 * s + 3) * s := Nat.mul_le_mul (by omega) hG
  have e : (4 * s + 3) * s = 4 * s ^ 2 + 3 * s := by ring
  have e2 : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
  omega

section Word
variable (D : HashData) (hD : DataOk D) (c : HbCaps) (plen pfx : ℕ)
include hD

theorem tb_le (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) :
    ((hbX D c plen pfx).tbOf cc).length ≤ 1100 * (hbS D + 1) ^ 3 := by
  have hx : (hbX D c plen pfx).xOf cc ≤ hbS D := (cell_x D c plen pfx cc).trans (hbS_Tl D)
  have hT2 : 2 * D.MP.t ≤ hbS D := hbS_T2 D
  have hwt : (wtWord (hbX D c plen pfx).Ws).length ≤ hbS D := hbS_wt D
  have hht : (htWord (hbX D c plen pfx).Fs).length ≤ hbS D := hbS_ht D
  have hq : (hbX D c plen pfx).qOf cc < D.N ^ 2 := cell_q D c plen pfx cc hc
  have hN2 := hbS_N2 D
  have hG : (hbX D c plen pfx).G ≤ hbS D := hbS_G D
  have hlam := cell_lam D c plen pfx cc
  unfold HbX.tbOf termBits
  simp only [List.length_append, List.length_cons, List.length_nil, coefBits_length]
  have hw : (frame ((hbX D c plen pfx).Ws.getD ((hbX D c plen pfx).lamOf cc) [])).length ≤
      (wtWord (hbX D c plen pfx).Ws).length := by
    have hl : (hbX D c plen pfx).lamOf cc < (hbX D c plen pfx).Ws.length := by
      show (hbX D c plen pfx).lamOf cc < (wsOf D.MP).length
      simp only [wsOf, List.length_map, List.length_range]; omega
    rw [List.getD_eq_getElem _ _ hl]
    exact frame_le_wt _ _ hl
  have hF : (polyWord ((hbX D c plen pfx).Fs.getD ((hbX D c plen pfx).idxOf cc) [])).length ≤
      (htWord (hbX D c plen pfx).Fs).length := polyWord_le_ht _ _
  have hmr : monoRoom (4 * (hbX D c plen pfx).qOf cc) (hbX D c plen pfx).G (hbX D c plen pfx).G ≤
      106 * (hbS D + 1) ^ 2 := monoRoom_le _ _ (hbS D) (by omega) hG
  have hz : ∀ i ∈ (hbX D c plen pfx).ιsOf cc, (zRec (hbX D c plen pfx).G ((hbX D c plen pfx).qOf cc)
      ((hbX D c plen pfx).popOf cc).1 (((hbX D c plen pfx).popOf cc).2.getD i 0)).length ≤
      10 * (106 * (hbS D + 1) ^ 2) + 2 := by
    intro i _
    have hgi : ((hbX D c plen pfx).popOf cc).2.getD i 0 ≤ (hbX D c plen pfx).G := by
      by_cases hi : i < ((hbX D c plen pfx).popOf cc).2.length
      · rw [List.getD_eq_getElem _ _ hi]
        have hp := cell_p D c plen pfx cc hc
        have hmem : (hbX D c plen pfx).popOf cc ∈ D.pops := by
          show D.pops.getD ((hbX D c plen pfx).pOf cc) (false, []) ∈ D.pops
          rw [List.getD_eq_getElem _ _ hp]
          exact List.getElem_mem hp
        exact hD.hG _ hmem _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
    have := zRec_length_le (hbX D c plen pfx).G ((hbX D c plen pfx).qOf cc)
      (((hbX D c plen pfx).popOf cc).2.getD i 0) ((hbX D c plen pfx).popOf cc).1 hgi
    omega
  have hzs : (((hbX D c plen pfx).ιsOf cc).flatMap fun i => zRec (hbX D c plen pfx).G ((hbX D c plen pfx).qOf cc)
      ((hbX D c plen pfx).popOf cc).1 (((hbX D c plen pfx).popOf cc).2.getD i 0)).length ≤
      ((hbX D c plen pfx).ιsOf cc).length * (10 * (106 * (hbS D + 1) ^ 2) + 2) := by
    rw [List.length_flatMap]
    have := List.sum_le_sum (l := (hbX D c plen pfx).ιsOf cc) (f := fun i => (zRec (hbX D c plen pfx).G
      ((hbX D c plen pfx).qOf cc) ((hbX D c plen pfx).popOf cc).1
      (((hbX D c plen pfx).popOf cc).2.getD i 0)).length) (g := fun _ => 10 * (106 * (hbS D + 1) ^ 2) + 2) hz
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
    exact this
  have hιl : ((hbX D c plen pfx).ιsOf cc).length = 2 * D.MP.t := by simp [HbX.ιsOf]; rfl
  rw [hιl] at hzs
  have hm : 2 * D.MP.t * (10 * (106 * (hbS D + 1) ^ 2) + 2) ≤ (hbS D + 1) * (1062 * (hbS D + 1) ^ 2) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (hbS D + 1) (by omega); omega)
  have e3 : (hbS D + 1) * (1062 * (hbS D + 1) ^ 2) = 1062 * (hbS D + 1) ^ 3 := by ring
  have p13 : hbS D + 1 ≤ (hbS D + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem cellWord_le (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) :
    ((hbX D c plen pfx).cellWord cc).length ≤ 1100 * (hbS D + 1) ^ 3 := by
  unfold HbX.cellWord
  split_ifs
  · exact tb_le D hD c plen pfx cc hc
  · simp

/-- **The output before cell `cc ≤ n`**. -/
theorem outAt_le (cc : ℕ) (hc : cc ≤ (hbX D c plen pfx).n) :
    ((hbX D c plen pfx).outAt cc).length ≤ 1100 * (hbS D + 1) ^ 4 := by
  have key : ∀ k, k ≤ (hbX D c plen pfx).n →
      ((hbX D c plen pfx).outAt k).length ≤ k * (1100 * (hbS D + 1) ^ 3) := by
    intro k
    induction k with
    | zero => intro _; simp [HbX.outAt]
    | succ k ih =>
      intro hk
      rw [HbX.outAt_succ, List.length_append]
      have h1 := ih (by omega)
      have h2 := cellWord_le D hD c plen pfx k (by omega)
      rw [Nat.succ_mul]
      omega
  have h := key cc hc
  have hn := hbS_n D c plen pfx
  have : cc * (1100 * (hbS D + 1) ^ 3) ≤ (hbS D + 1) * (1100 * (hbS D + 1) ^ 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (hbS D + 1) * (1100 * (hbS D + 1) ^ 3) = 1100 * (hbS D + 1) ^ 4 := by ring
  omega

end Word

end NearCubicWires.WireExponent3_5.PrimT.C4HB
