import Proof.Wire_3_5.Primitive.Writers.SFCost3

/-! # polynomial bounds on the SeedFix stages' step counts, part 4 (the enumeration's cells)

`elimCost_le'` (the elimination at every argument `≤ q`, the prefix not assumed `≤ 2h·ℓ`), `splitCost_le`, and the
cell costs of the enumeration, `groupCost`, `restCost`, `JEnum.cellCost`, `JBody.jCost`, under `GroupSmall q X j V`
(the call's numbers and the group's sizes `≤ q`, the size lemmas discharge it).

Paper quantity: none (the step counts of `samp:seed`'s enumeration cells, P3:3011-3016, 3034-3038). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SFCost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)
open NearCubicWires.WireExponent3_5.SeedFix.JBody

/-- **The elimination's cost** at every argument `≤ q`. -/
theorem elimCost_le' (ℓ twoH k plen n q : ℕ) (hl : ℓ ≤ q) (ht : twoH ≤ q) (hk : k ≤ q) (hp : plen ≤ q) (hn : n ≤ q) :
    elimCost ℓ twoH k plen n ≤ 1900 * (q + 1) ^ 6 := by
  unfold elimCost rowsAllCost countCost
  have h1 := loopCost_le ℓ twoH k plen n q hl ht hk hp hn
  have hnk : n * k ≤ (q + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hr : twoH * ℓ - plen ≤ (q + 1) ^ 2 :=
    le_trans (Nat.sub_le _ _) (by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega))
  have hg := Gauss.gaussCost_le (n * k) (twoH * ℓ - plen) ((q + 1) ^ 2) (Nat.one_le_pow _ _ (by omega)) hnk hr
  have e6 : ((q + 1) ^ 2) ^ 3 = (q + 1) ^ 6 := by ring
  rw [e6] at hg
  have hd : Deficit.cost (twoH * ℓ - plen) ≤ 3 * (q + 1) ^ 2 + 3 := by unfold Deficit.cost; omega
  have p56 := pw (q + 1) 5 6 (by omega) (by norm_num)
  have p26 := pw (q + 1) 2 6 (by omega) (by norm_num)
  have p06 : 1 ≤ (q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The group's sizes: the call's numbers, the group's counts and the fold states of its fetches within `q`. -/
def GroupSmall (q : ℕ) (X : JCtx) (j : ℕ) (V : SExpr) : Prop :=
  X.P.ell ≤ q ∧ 2 * X.P.kh ≤ q ∧ 8 ≤ q ∧ X.plen ≤ q ∧ (X.consJ j).length ≤ q ∧ X.eJ j ≤ q ∧ X.TWd ≤ q ∧ X.Wt ≤ q ∧
    (X.esJ j).length ≤ q ∧ EntsSmall q X.ents ∧
    (∀ k, k < (X.esJ j).length →
      FoldSmall q (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) k) (X.ents.getD ((X.esJ j).getD k 0) []) ∧
        ((X.csJ j).getD k []).length ≤ q) ∧
    (exprWord V).length ≤ q ∧
    (exprWord (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length ≤ q

/-- **The group's cost.** -/
theorem groupCost_le (X : JCtx) (j : ℕ) (V : SExpr) (q : ℕ) (h : GroupSmall q X j V) :
    groupCost X j V ≤ 2600 * (q + 1) ^ 6 := by
  obtain ⟨hl, hk, h8, hp, hc, he, hT, hW, hes, hE, hF, hV, hA⟩ := h
  unfold groupCost
  have g1 := consInnerCost_le 8 X.P.ell (2 * X.P.kh) q h8 hl hk
  have g2 := elimCost_le' X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length q hl h8 hk hp hc
  have g3 := coefCost_le (RepairOrdinary.SignedSortKey.binary 8 j) (2 * X.P.kh) (X.eJ j) q
    (by rw [RepairOrdinary.SignedSortKey.binary_length]; exact h8) hk he
  have g4 := fetchCellsCost_le (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j)
    (RepairOrdinary.SignedSortKey.binary X.TWd X.t) X.Wt q hW hE hes hF
    (by rw [RepairOrdinary.SignedSortKey.binary_length]; exact hT)
  have g5 := emitInnerCost_le (exprWord V).length
    (exprWord (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length q hV hA
  have p26 := pw (q + 1) 2 6 (by omega) (by norm_num)
  have p16 := pw (q + 1) 1 6 (by omega) (by norm_num)
  have p06 : 1 ≤ (q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rw [pow_one] at g5 p16
  split_ifs <;> omega

theorem restCost_le (X : JCtx) (j : ℕ) (V : SExpr) (q : ℕ) (h : GroupSmall q X j V) (hkh : X.P.kh ≤ q) :
    JEnum.restCost X j V ≤ 2900 * (q + 1) ^ 6 := by
  have h8 := h.2.2.1
  have hl := h.1
  unfold JEnum.restCost
  have g1 := cellsInnerCost_le X.P.kh q hkh
  have g2 := validInnerCost_le 8 X.P.ell q h8 hl
  have g3 := groupCost_le X j V q h
  have p26 := pw (q + 1) 2 6 (by omega) (by norm_num)
  have p16 := pw (q + 1) 1 6 (by omega) (by norm_num)
  rw [pow_one] at g1 p16
  split_ifs <;> omega

/-- **The enumeration's cell cost** (the split with the state word, the rest at the cell's state, the increment). -/
theorem cellCost_le (X : JCtx) (j : ℕ) (V : SExpr) (q : ℕ)
    (h : GroupSmall q (SplitT.at_ X (SplitT.tOf X j)) j V) (hkh : X.P.kh ≤ q) (hw : SplitT.wT X ≤ q) :
    JEnum.cellCost X j V ≤ 6000 * (q + 1) ^ 6 := by
  have hl : X.P.ell ≤ q := h.1
  have hT : X.TWd ≤ q := h.2.2.2.2.2.2.1
  unfold JEnum.cellCost
  have g1 := splitTCost_le X.P.ell X.P.kh X.TWd q hl hkh hT
  have g2 := restCost_le (SplitT.at_ X (SplitT.tOf X j)) j V q h hkh
  have p16 := pw (q + 1) 1 6 (by omega) (by norm_num)
  rw [pow_one] at g1 p16
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SFCost
