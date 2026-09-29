import Proof.Wire_3_5.Primitive.Writers.SFCost2
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixJEnum

/-! # polynomial bounds on the SeedFix stages' step counts, part 3 (the fold and the fetches)

The data-dependent costs, in their own sizes (the split: his size lemmas discharge the size predicates):
* `ESz q V` (the expression's word and term count `≤ q`), `FoldSmall q s₀ rs` (the rows, their fold states and
  products `≤ q`), `EntsSmall q ents` (the entries and their rows' words `≤ q`);
* `mulCost_le`, `fRowCost_le`, `rowsMulCost_le`, `rowsSkipCost_le`, `entCost_le`, `fetchCost_le`, `fetchAllCost_le`,
  `fcCost_le`, `fetchCellsCost_le`: each `≤ C·(q+1)^D`.

Paper quantity: none (the step counts of `samp:seed`'s enumeration, P3:3011-3016, 3034-3038). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SFCost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)

/-- An expression's size: its word and its term count. -/
def ESz (q : ℕ) (V : SExpr) : Prop := (exprWord V).length ≤ q ∧ V.length ≤ q

/-- The rows of an entry folded from `s₀`: their count, each fold state, each row and each product within `q`. -/
def FoldSmall (q : ℕ) (s0 : FoldSt) (rs : List SExpr) : Prop :=
  rs.length ≤ q ∧ ∀ r, r < rs.length → ESz q (foldAt s0 rs r).A ∧ ESz q (rs.getD r []) ∧
    (exprWord (smul (foldAt s0 rs r).A (rs.getD r []))).length ≤ q

/-- The entries: their count, each entry's row count and each row's word within `q`. -/
def EntsSmall (q : ℕ) (ents : List (List SExpr)) : Prop :=
  ents.length ≤ q ∧ ∀ j, j < ents.length → (ents.getD j []).length ≤ q ∧ ∀ V ∈ ents.getD j [], (exprWord V).length ≤ q

theorem sum_range_le (n c : ℕ) (f : ℕ → ℕ) (h : ∀ i, i < n → f i ≤ c) :
    ((List.range n).map f).sum ≤ n * c := by
  have := List.sum_le_card_nsmul ((List.range n).map f) c (fun y hy => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact h i (List.mem_range.mp hi))
  simpa using this

theorem mulCost_le (V W : SExpr) (q : ℕ) (hV : ESz q V) (hW : ESz q W) : mulCost V W ≤ 80 * (q + 1) ^ 3 := by
  obtain ⟨a1, a2⟩ := hV
  obtain ⟨b1, b2⟩ := hW
  unfold mulCost mOuterCost tcBound ilBound ibound
  have h1 : W.length * (2 * ((exprWord V).length + (exprWord W).length + 6) + 2 + 2) ≤ q * (4 * q + 16) :=
    Nat.mul_le_mul b2 (by omega)
  have hO : 1 + 1 + (2 * ((exprWord V).length + 5) + 2) + 1 +
      (2 * (W.length * (2 * ((exprWord V).length + (exprWord W).length + 6) + 2 + 2) + 1) + 2) ≤ 34 * (q + 1) ^ 2 := by
    nlinarith
  have h2 : V.length * (1 + 1 + (2 * ((exprWord V).length + 5) + 2) + 1 +
      (2 * (W.length * (2 * ((exprWord V).length + (exprWord W).length + 6) + 2 + 2) + 1) + 2) + 2) ≤
      q * (34 * (q + 1) ^ 2 + 2) := Nat.mul_le_mul a2 (by omega)
  have e : q * (34 * (q + 1) ^ 2 + 2) + 3 ≤ 36 * (q + 1) ^ 3 := by nlinarith
  omega

theorem fRowCost_le (s : FoldSt) (V : SExpr) (q : ℕ) (hA : ESz q s.A) (hV : ESz q V)
    (hP : (exprWord (smul s.A V)).length ≤ q) : fRowCost s V ≤ 90 * (q + 1) ^ 3 := by
  unfold fRowCost
  have h1 := mulCost_le s.A V q hA hV
  have p13 := pw (q + 1) 1 3 (by omega) (by norm_num)
  rw [pow_one] at p13
  have := hV.1
  omega

theorem rowsMulCost_le (s0 : FoldSt) (rs : List SExpr) (q : ℕ) (h : FoldSmall q s0 rs) :
    rowsMulCost s0 rs ≤ 93 * (q + 1) ^ 4 := by
  obtain ⟨hl, hr⟩ := h
  unfold rowsMulCost
  have hs := sum_range_le (rs.length - 0) (90 * (q + 1) ^ 3 + 2)
    (fun i => fRowCost (foldAt s0 rs (0 + i)) (rs.getD (0 + i) []) + 2) (fun i hi => by
      obtain ⟨a, b, c⟩ := hr (0 + i) (by omega)
      have := fRowCost_le (foldAt s0 rs (0 + i)) (rs.getD (0 + i) []) q a b c
      omega)
  have h2 : (rs.length - 0) * (90 * (q + 1) ^ 3 + 2) ≤ (q + 1) * (92 * (q + 1) ^ 3) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 3 (q + 1) (by omega); omega)
  have e : (q + 1) * (92 * (q + 1) ^ 3) = 92 * (q + 1) ^ 4 := by ring
  have p04 : 1 ≤ (q + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

theorem rowsSkipCost_le (rs : List SExpr) (q : ℕ) (hl : rs.length ≤ q)
    (hV : ∀ V ∈ rs, (exprWord V).length ≤ q) : rowsSkipCost rs ≤ 5 * (q + 1) ^ 2 := by
  unfold rowsSkipCost
  have hs := sum_range_le (rs.length - 0) (q + 4) (fun i => 1 + 1 + (exprWord (rs.getD (0 + i) [])).length + 2)
    (fun i hi => by
      have hm : rs.getD (0 + i) [] ∈ rs := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have := hV _ hm
      omega)
  have h2 : (rs.length - 0) * (q + 4) ≤ (q + 1) * (4 * (q + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have e : (q + 1) * (4 * (q + 1)) = 4 * (q + 1) ^ 2 := by ring
  have p02 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem entCost_le (s0 : FoldSt) (ents : List (List SExpr)) (W e j q : ℕ) (hW : W ≤ q) (hE : EntsSmall q ents)
    (hF : FoldSmall q s0 (ents.getD e [])) : entCost s0 ents W e j ≤ 115 * (q + 1) ^ 4 := by
  have hR : (if j = e then rowsMulCost s0 (ents.getD j []) else rowsSkipCost (ents.getD j [])) ≤ 93 * (q + 1) ^ 4 := by
    split_ifs with hj
    · subst hj; exact rowsMulCost_le s0 _ q hF
    · by_cases hjl : j < ents.length
      · obtain ⟨h1, h2⟩ := hE.2 j hjl
        have := rowsSkipCost_le (ents.getD j []) q h1 h2
        have := pw (q + 1) 2 4 (by omega) (by norm_num)
        omega
      · rw [List.getD_eq_default _ _ (by omega)]
        unfold rowsSkipCost
        have := Nat.one_le_pow 4 (q + 1) (by omega)
        simp; omega
  unfold entCost
  have p14 := pw (q + 1) 1 4 (by omega) (by norm_num)
  rw [pow_one] at p14
  omega

theorem fetchCost_le (s0 : FoldSt) (ents : List (List SExpr)) (W e q : ℕ) (hW : W ≤ q) (hE : EntsSmall q ents)
    (hF : FoldSmall q s0 (ents.getD e [])) : FetchAll.fetchCost s0 ents W e ≤ 118 * (q + 1) ^ 5 := by
  unfold FetchAll.fetchCost
  have hs := sum_range_le (ents.length - 0) (115 * (q + 1) ^ 4 + 2) (fun i => entCost s0 ents W e (0 + i) + 2)
    (fun i hi => by have := entCost_le s0 ents W e (0 + i) q hW hE hF; omega)
  have h2 : (ents.length - 0) * (115 * (q + 1) ^ 4 + 2) ≤ (q + 1) * (117 * (q + 1) ^ 4) :=
    Nat.mul_le_mul (by have := hE.1; omega) (by have := Nat.one_le_pow 4 (q + 1) (by omega); omega)
  have e1 : (q + 1) * (117 * (q + 1) ^ 4) = 117 * (q + 1) ^ 5 := by ring
  have p05 : 1 ≤ (q + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  omega

theorem fetchAllCost_le (s0 : FoldSt) (ents : List (List SExpr)) (W e q : ℕ) (hW : W ≤ q) (hE : EntsSmall q ents)
    (hF : FoldSmall q s0 (ents.getD e [])) : FetchAll.fetchAllCost s0 ents W e ≤ 260 * (q + 1) ^ 5 := by
  unfold FetchAll.fetchAllCost
  have h1 := fetchCost_le s0 ents W e q hW hE hF
  have p15 := pw (q + 1) 1 5 (by omega) (by norm_num)
  rw [pow_one] at p15
  omega

theorem fcCost_le (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool)) (tw : List Bool)
    (W k q : ℕ) (hW : W ≤ q) (hE : EntsSmall q ents)
    (hF : FoldSmall q (FetchCells.fcSt s0 ents es k) (ents.getD (es.getD k 0) []))
    (hc : (cs.getD k []).length ≤ q) (ht : tw.length ≤ q) :
    FetchCells.fcCost s0 ents es cs tw W k ≤ 280 * (q + 1) ^ 5 := by
  unfold FetchCells.fcCost
  have h1 := fetchAllCost_le (FetchCells.fcSt s0 ents es k) ents W (es.getD k 0) q hW hE hF
  have h2 := tgtInnerCost_le (cs.getD k []).length tw.length q hc ht
  have p15 := pw (q + 1) 1 5 (by omega) (by norm_num)
  rw [pow_one] at h2 p15
  omega

theorem fetchCellsCost_le (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool))
    (tw : List Bool) (W q : ℕ) (hW : W ≤ q) (hE : EntsSmall q ents) (hes : es.length ≤ q)
    (hF : ∀ k, k < es.length → FoldSmall q (FetchCells.fcSt s0 ents es k) (ents.getD (es.getD k 0) []) ∧
      (cs.getD k []).length ≤ q) (ht : tw.length ≤ q) :
    FetchCells.fetchCellsCost s0 ents es cs tw W ≤ 570 * (q + 1) ^ 6 := by
  unfold FetchCells.fetchCellsCost
  have hs := sum_range_le (es.length - 0) (280 * (q + 1) ^ 5 + 2) (fun i => FetchCells.fcCost s0 ents es cs tw W (0 + i) + 2)
    (fun i hi => by
      obtain ⟨a, b⟩ := hF (0 + i) (by omega)
      have := fcCost_le s0 ents es cs tw W (0 + i) q hW hE a b ht
      omega)
  have h2 : (es.length - 0) * (280 * (q + 1) ^ 5 + 2) ≤ (q + 1) * (282 * (q + 1) ^ 5) :=
    Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 5 (q + 1) (by omega); omega)
  have e1 : (q + 1) * (282 * (q + 1) ^ 5) = 282 * (q + 1) ^ 6 := by ring
  have p06 : 1 ≤ (q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SFCost
