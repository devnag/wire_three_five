import Proof.Wire_3_5.Primitive.SeedFix.C4HB
import Proof.Wire_3_5.Primitive.Writers.SFCost4

/-! # C4HB, part 1: the printer's small numbers and words below the data size

P3:2262-2268 (the Hb printer's cells). With `s = hbS D`: the odometer's width `2t + 2tℓ₀`, `2t`, `2tℓ₀`, `ℓ₀`,
`2^{ℓ₀+1}`, `J`, the words `htWord`, `popsWord`, `wtWord`, `G`, `N²`, `nE`, `|pops|` and the cell count are at most
`s`; at every cell `c < n` its counters, its elimination width and its HASH row index are in range.

* `lt_pow2`, `hbS_T2`, `hbS_Tl`, `hbS_L`, `hbS_l`, `hbS_l2`, `hbS_J`, `hbS_ht`, `hbS_pw`, `hbS_wt`, `hbS_G`,
  `hbS_N2`, `hbS_nE`, `hbS_P`, `hbS_n`; `cell_lam`, `cell_p`, `cell_e`, `cell_q`, `cell_x`, `cell_k`, `cell_idx`,
  `cell_pop`.

Paper quantity: none (the Hb printer's sizes). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM

theorem lt_pow2 : ∀ x : ℕ, x < 2 ^ x
  | 0 => by norm_num
  | x + 1 => by have := lt_pow2 x; rw [pow_succ]; omega

theorem len_le_flatMap {α β : Type} (f : α → List β) : ∀ (l : List α) (x : α), x ∈ l → (f x).length ≤ (l.flatMap f).length
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, x, h => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := len_le_flatMap f l x h; omega

theorem length_le_popsWord : ∀ pops : List (Bool × List ℕ), pops.length ≤ (popsWord pops).length
  | [] => by simp [popsWord]
  | p :: ps => by
    have := length_le_popsWord ps
    simp only [popsWord, List.flatMap_cons, List.length_append, List.length_cons] at this ⊢
    simp only [popRec, List.length_append, List.length_cons] at *
    omega

theorem gates_le_flat : ∀ l : List ℕ, l.length ≤ (l.flatMap elemW).length
  | [] => by simp
  | a :: l => by
    have := gates_le_flat l
    rw [List.flatMap_cons, List.length_append, elemW_length, List.length_cons]
    omega

theorem gates_le_popRec (pop : Bool × List ℕ) : pop.2.length ≤ (popRec pop).length := by
  unfold popRec
  simp only [List.length_append, List.length_cons, List.length_nil]
  have := gates_le_flat pop.2
  omega

section Basic
variable (D : HashData)

/-- `hbS` with its two powers named. -/
theorem hbS_eq : ∃ B C : ℕ, B = 2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) ∧ C = 2 ^ (D.MP.ell0 + 1) ∧
    hbS D = B * (D.MP.J + 1) * D.pops.length * D.nE * D.N ^ 2 + B + C + (htWord D.Fs).length +
      (popsWord D.pops).length + (wtWord (wsOf D.MP)).length + D.G + D.N ^ 2 + D.nE :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem hbS_B : 2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) ≤ hbS D := by
  obtain ⟨B, C, hB, _, h⟩ := hbS_eq D; rw [h, ← hB]; omega
theorem hbS_L : 2 * D.MP.t + 2 * D.MP.t * D.MP.ell0 ≤ hbS D :=
  (lt_pow2 _).le.trans (hbS_B D)
theorem hbS_T2 : 2 * D.MP.t ≤ hbS D := by have := hbS_L D; omega
theorem hbS_Tl : 2 * D.MP.t * D.MP.ell0 ≤ hbS D := by have := hbS_L D; omega
theorem hbS_l2 : 2 ^ (D.MP.ell0 + 1) ≤ hbS D := by
  obtain ⟨B, C, _, hC, h⟩ := hbS_eq D; rw [h, ← hC]; omega
theorem hbS_l1 : 2 ^ D.MP.ell0 ≤ hbS D := by
  have := hbS_l2 D; rw [pow_succ] at this; omega
theorem hbS_l : D.MP.ell0 ≤ hbS D := (lt_pow2 _).le.trans (hbS_l1 D)
theorem hbS_J : D.MP.J ≤ hbS D := (Filters.MajorantParams.J_lt_ell0 D.MP).le.trans (hbS_l D)
theorem hbS_ht : (htWord D.Fs).length ≤ hbS D := by obtain ⟨B, C, _, _, h⟩ := hbS_eq D; rw [h]; omega
theorem hbS_pw : (popsWord D.pops).length ≤ hbS D := by obtain ⟨B, C, _, _, h⟩ := hbS_eq D; rw [h]; omega
theorem hbS_wt : (wtWord (wsOf D.MP)).length ≤ hbS D := by obtain ⟨B, C, _, _, h⟩ := hbS_eq D; rw [h]; omega
theorem hbS_G : D.G ≤ hbS D := by obtain ⟨B, C, _, _, h⟩ := hbS_eq D; rw [h]; omega
theorem hbS_N2 : D.N ^ 2 ≤ hbS D := by obtain ⟨B, C, _, _, h⟩ := hbS_eq D; rw [h]; omega
theorem hbS_nE : D.nE ≤ hbS D := by obtain ⟨B, C, _, _, h⟩ := hbS_eq D; rw [h]; omega
theorem hbS_P : D.pops.length ≤ hbS D := (length_le_popsWord _).trans (hbS_pw D)

theorem hbS_n (c : HbCaps) (plen pfx : ℕ) : (hbX D c plen pfx).n ≤ hbS D := by
  show 2 ^ (2 * D.MP.t + 2 * D.MP.t * D.MP.ell0) * (D.MP.J + 1) * D.pops.length * D.nE * D.N ^ 2 ≤ hbS D
  obtain ⟨B, C, hB, _, h⟩ := hbS_eq D
  rw [h, ← hB]
  omega

end Basic

section Cell
variable (D : HashData) (c : HbCaps) (plen pfx : ℕ)

theorem cell_lam (cc : ℕ) : (hbX D c plen pfx).lamOf cc ≤ D.MP.J := by
  show cc / _ % (D.MP.J + 1) ≤ D.MP.J
  exact Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))

theorem cell_p (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) : (hbX D c plen pfx).pOf cc < D.pops.length := by
  have := (pos_of_lt_n (hbX D c plen pfx) cc hc).2.2.1
  exact Nat.mod_lt _ this

theorem cell_e (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) : (hbX D c plen pfx).eOf cc < D.nE := by
  have := (pos_of_lt_n (hbX D c plen pfx) cc hc).2.2.2.1
  exact Nat.mod_lt _ this

theorem cell_q (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) : (hbX D c plen pfx).qOf cc < D.N ^ 2 := by
  have := (pos_of_lt_n (hbX D c plen pfx) cc hc).2.2.2.2
  exact Nat.mod_lt _ this

theorem cell_x (cc : ℕ) : (hbX D c plen pfx).xOf cc ≤ 2 * D.MP.t * D.MP.ell0 := by
  show 2 * D.MP.t * D.MP.ell0 - plen - _ ≤ 2 * D.MP.t * D.MP.ell0
  omega

theorem cell_k (cc : ℕ) : (hbX D c plen pfx).kOfC cc ≤ D.MP.J := by
  show kOfL _ D.MP.J ≤ D.MP.J
  unfold kOfL
  have := cell_lam D c plen pfx cc
  split_ifs with h
  · omega
  · omega

theorem cell_idx (cc : ℕ) (hc : cc < (hbX D c plen pfx).n) :
    (hbX D c plen pfx).idxOf cc < D.N ^ 2 * D.nE := by
  have he := cell_e D c plen pfx cc hc
  have hq := cell_q D c plen pfx cc hc
  show (hbX D c plen pfx).eOf cc + (hbX D c plen pfx).qOf cc * D.nE < D.N ^ 2 * D.nE
  have : ((hbX D c plen pfx).qOf cc + 1) * D.nE ≤ D.N ^ 2 * D.nE := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, one_mul] at this
  omega

theorem cell_pop (cc : ℕ) : ((hbX D c plen pfx).popOf cc).2.length ≤ (popsWord D.pops).length := by
  show ((D.pops).getD ((hbX D c plen pfx).pOf cc) (false, [])).2.length ≤ _
  by_cases h : (hbX D c plen pfx).pOf cc < D.pops.length
  · rw [List.getD_eq_getElem _ _ h]
    refine (gates_le_popRec _).trans ((len_le_flatMap popRec D.pops _ (List.getElem_mem h)).trans ?_)
    unfold popsWord; simp
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

end Cell

end NearCubicWires.WireExponent3_5.PrimT.C4HB
