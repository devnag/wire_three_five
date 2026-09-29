import Proof.Wire_3_5.Primitive.SeedFix.C4GrpD
import Proof.Wire_3_5.Primitive.Writers.SFCost4

/-! # The enumeration's side conditions at a call, generic in the batch, part 1: the group's capacities

P3:3011-3016 (the enumeration of `samp:seed`'s cells: every capacity of the group's machines is at least the
group's step counts). With the group's sizes within `q` (`GroupSmall`, `groupSmall_of` at `qG`), every
capacity field of `C4Grp.GroupCaps` holds once each capacity is at least `capC·(q+1)^6` (the cost bounds).
Mode-generic: no SYM, THR or HASH fact is used.

* `capC`, `addQ`, `mulQ`, `fin6`, **`rowCaps_of`**, **`groupCaps_small`**.

Paper quantity of the main type: the group's machine capacities against its step counts. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.Cost
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages JBody SplitT JEnum

/-- The capacity constant: every capacity at least `capC·(q+1)^6`. -/
def capC : ℕ := 100000

theorem addQ {x c k Q : ℕ} (d : ℕ) (hQ : 1 ≤ Q) (hx : x ≤ c * Q ^ k) : x + d ≤ (c + d) * Q ^ k := by
  have h1 : 1 ≤ Q ^ k := Nat.one_le_pow _ _ hQ
  have h2 : d ≤ d * Q ^ k := Nat.le_mul_of_pos_right _ h1
  have e : (c + d) * Q ^ k = c * Q ^ k + d * Q ^ k := by ring
  omega

theorem mulQ {a b c k Q : ℕ} (ha : a ≤ Q) (hb : b ≤ c * Q ^ k) : a * b ≤ c * Q ^ (k + 1) := by
  calc a * b ≤ Q * (c * Q ^ k) := Nat.mul_le_mul ha hb
    _ = c * Q ^ (k + 1) := by ring

theorem fin6 {x c k Q C : ℕ} (hx : x ≤ c * Q ^ k) (hk : k ≤ 6) (hQ : 1 ≤ Q) (hc : c ≤ capC)
    (hC : capC * Q ^ 6 ≤ C) : x ≤ C := by
  have h1 : Q ^ k ≤ Q ^ 6 := Nat.pow_le_pow_right hQ hk
  have h2 : c * Q ^ k ≤ capC * Q ^ 6 := Nat.mul_le_mul hc h1
  omega

/-- **One row's capacities** (`FoldRows.RowCaps`) from the fold state's, the row's and the product's sizes. -/
theorem rowCaps_of (s : FoldSt) (V : SExpr) (q cI cT cA cC : ℕ) (hA : PrimAsm.SFCost.ESz q s.A) (hV : PrimAsm.SFCost.ESz q V)
    (hP : (exprWord (smul s.A V)).length ≤ q) (hI : 64 * (q + 1) ^ 3 ≤ cI) (hT : 64 * (q + 1) ^ 3 ≤ cT)
    (hA' : 64 * (q + 1) ^ 3 ≤ cA) (hC : 64 * (q + 1) ^ 3 ≤ cC) : RowCaps s V cI cT cA cC := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hV1, hV2⟩ := hV
  have e : 64 * (q + 1) ^ 3 = q * (2 * (q * (4 * q + 16)) + 2 * q + 21) + 3 +
      (56 * (q * q * q) + 158 * (q * q) + 171 * q + 61) := by ring
  have hb : q * (2 * (q * (4 * q + 16)) + 2 * q + 21) + 3 ≤ 64 * (q + 1) ^ 3 :=
    (Nat.le_add_right _ _).trans_eq e.symm
  have hb2 : q * (4 * q + 16) + 1 ≤ q * (2 * (q * (4 * q + 16)) + 2 * q + 21) + 3 := by
    have : q * (4 * q + 16) ≤ 2 * (q * (4 * q + 16)) + 2 * q + 21 := by omega
    have h8 : q * (4 * q + 16) ≤ q * (4 * q + 16) * 1 := by omega
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; simp
    · have := Nat.mul_le_mul_left q this
      have h9 : q * (4 * q + 16) ≤ q * (q * (4 * q + 16)) := Nat.le_mul_of_pos_left _ h0
      omega
  have hI0 : ilBound s.A V ≤ q * (4 * q + 16) + 1 := by
    unfold ilBound ibound
    have := Nat.mul_le_mul hV2 (show 2 * ((exprWord s.A).length + (exprWord V).length + 6) + 2 + 2 ≤ 4 * q + 16 by
      omega)
    omega
  have hM : mOuterCost s.A V ≤ 2 * (q * (4 * q + 16)) + 2 * q + 19 := by
    unfold mOuterCost tcBound
    omega
  have hO : s.A.length * (mOuterCost s.A V + 2) ≤ q * (2 * (q * (4 * q + 16)) + 2 * q + 21) :=
    Nat.mul_le_mul hA2 (by omega)
  have hWq : 4 * q + 8 ≤ 64 * (q + 1) ^ 3 := by
    have : q + 1 ≤ (q + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  generalize q * (2 * (q * (4 * q + 16)) + 2 * q + 21) = Z at hb hb2 hO
  generalize q * (4 * q + 16) = Y at hb2 hI0 hM
  generalize 64 * (q + 1) ^ 3 = W at hb hI hT hA' hC hWq
  unfold RowCaps tcBound ibound
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The group's capacity fields** from its sizes: every capacity at least `capC·(q+1)^6`. -/
theorem groupCaps_small (X : JCtx) (j : ℕ) (S : JState) (V : SExpr) (q : ℕ) (h : PrimAsm.SFCost.GroupSmall q X j V)
    (hm : 1 ≤ X.m) (hK : 8 * X.P.ell - X.plen ≤ X.cK)
    (h0 : capC * (q + 1) ^ 6 ≤ X.c0) (h1 : capC * (q + 1) ^ 6 ≤ X.c1) (h2 : capC * (q + 1) ^ 6 ≤ X.c2)
    (h3 : capC * (q + 1) ^ 6 ≤ X.c3) (h4 : capC * (q + 1) ^ 6 ≤ X.c4) (h5 : capC * (q + 1) ^ 6 ≤ X.c5)
    (h6 : capC * (q + 1) ^ 6 ≤ X.c6) (h7 : capC * (q + 1) ^ 6 ≤ X.c7) :
    PrimT.C4Grp.GroupCaps X j S V := by
  obtain ⟨hl, hk, h8, hp, hc, he, hT, hW, hes, hE, hF, hV, hA⟩ := h
  have hQ : 1 ≤ q + 1 := by omega
  have cQ : ∀ {x : ℕ}, x ≤ q → x ≤ 1 * (q + 1) ^ 1 := fun hx => by rw [pow_one, Nat.one_mul]; omega
  have hcap6 : capC ≤ capC := le_rfl
  -- q·q ≤ (q+1)²
  have hqq : q * q ≤ 1 * (q + 1) ^ 2 := by
    rw [Nat.one_mul, sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h8l : 8 * X.P.ell ≤ q * q := Nat.mul_le_mul h8 hl
  -- the fields
  have f1 : Cons.consInnerCost 8 X.P.ell (2 * X.P.kh) ≤ X.c0 :=
    fin6 (PrimAsm.SFCost.consInnerCost_le 8 X.P.ell (2 * X.P.kh) q h8 hl hk) (by norm_num) hQ (by unfold capC; norm_num) h0
  have f2 : 2 * X.P.ell + 2 ≤ X.c0 :=
    fin6 (show 2 * X.P.ell + 2 ≤ 4 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ (by unfold capC; norm_num) h0
  have f3 : X.P.ell * (innerCost X.P.ell + 2) + 1 ≤ X.c1 :=
    fin6 (addQ 1 hQ (mulQ (show X.P.ell ≤ q + 1 by omega) (addQ 2 hQ (PrimAsm.SFCost.innerCost_le X.P.ell q hl))))
      (by norm_num) hQ (by unfold capC; norm_num) h1
  have f4 : X.P.ell * (GF2.mulIterCost X.P.ell + 2) + 1 ≤ X.c1 :=
    fin6 (addQ 1 hQ (mulQ (show X.P.ell ≤ q + 1 by omega) (addQ 2 hQ (PrimAsm.SFCost.mulIterCost_le X.P.ell q hl))))
      (by norm_num) hQ (by unfold capC; norm_num) h1
  have f5 : X.plen * (phACost X.P.ell + 2) + 1 ≤ X.c1 :=
    fin6 (addQ 1 hQ (mulQ (show X.plen ≤ q + 1 by omega) (addQ 2 hQ (PrimAsm.SFCost.phACost_le X.P.ell q hl))))
      (by norm_num) hQ (by unfold capC; norm_num) h1
  have f6 : tableCost X.P.ell 8 ≤ X.c2 := by
    have t1 := tableCost_le X.P.ell 8 q (by omega) hl h8
    have t2 : q ^ 3 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    exact fin6 (show tableCost X.P.ell 8 ≤ 203 * (q + 1) ^ 3 by omega) (by norm_num) hQ (by unfold capC; norm_num) h2
  have hn8 : 8 * X.P.ell ≤ (q + 1) ^ 2 := by rw [Nat.one_mul] at hqq; omega
  have f7 : passesCost X.P.ell X.plen (8 * X.P.ell) ≤ X.c2 :=
    fin6 (PrimAsm.SFCost.passesCost_le' X.P.ell X.plen (8 * X.P.ell) q hl hp hn8) (by norm_num) hQ
      (by unfold capC; norm_num) h2
  have f8 : 2 * X.P.kh * (rowCost X.P.ell X.plen (8 * X.P.ell) + 2) + 1 ≤ X.c4 :=
    fin6 (addQ 1 hQ (mulQ (show 2 * X.P.kh ≤ q + 1 by omega)
      (addQ 2 hQ (PrimAsm.SFCost.rowCost_le' X.P.ell X.plen (8 * X.P.ell) q hl hp hn8))))
      (by norm_num) hQ (by unfold capC; norm_num) h4
  have f9 : 2 * X.P.ell + 1 ≤ X.c3 :=
    fin6 (show 2 * X.P.ell + 1 ≤ 3 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ (by unfold capC; norm_num) h3
  have f10 : 2 * X.P.ell + 1 ≤ X.c5 :=
    fin6 (show 2 * X.P.ell + 1 ≤ 3 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ (by unfold capC; norm_num) h5
  have hv : 8 * X.P.ell - X.plen ≤ 8 * q := by omega
  have f11 : 2 * (8 * X.P.ell - X.plen) + 13 ≤ X.c0 :=
    fin6 (show 2 * (8 * X.P.ell - X.plen) + 13 ≤ 29 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ
      (by unfold capC; norm_num) h0
  have gr : Gauss.rowCost (8 * X.P.ell - X.plen) + 2 ≤ 226 * (q + 1) ^ 1 := by
    have := PrimAsm.SFCost.gaussRowCost_le (8 * X.P.ell - X.plen) (8 * q) hv
    rw [pow_one] at this ⊢
    omega
  have f12 : (X.consJ j).length * (2 * X.P.kh) * (Gauss.rowCost (8 * X.P.ell - X.plen) + 2) + 3 ≤ X.c1 := by
    have := mulQ (show (X.consJ j).length ≤ q + 1 by omega) (mulQ (show 2 * X.P.kh ≤ q + 1 by omega) gr)
    rw [← Nat.mul_assoc] at this
    exact fin6 (addQ 3 hQ this) (by norm_num) hQ (by unfold capC; norm_num) h1
  have f13 : (X.consJ j).length * (2 * X.P.kh) * (2 * (8 * X.P.ell - X.plen) + 1) + 1 ≤ X.c1 := by
    have := mulQ (show (X.consJ j).length ≤ q + 1 by omega) (mulQ (show 2 * X.P.kh ≤ q + 1 by omega)
      (show 2 * (8 * X.P.ell - X.plen) + 1 ≤ 17 * (q + 1) ^ 1 by rw [pow_one]; omega))
    rw [← Nat.mul_assoc] at this
    exact fin6 (addQ 1 hQ this) (by norm_num) hQ (by unfold capC; norm_num) h1
  have f14 : loopCost X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length + 1 + 1 ≤ X.c6 := by
    have := addQ 2 hQ (PrimAsm.SFCost.loopCost_le X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length q hl h8 hk hp hc)
    exact fin6 (show _ ≤ (756 + 2) * (q + 1) ^ 5 by omega) (by norm_num) hQ (by unfold capC; norm_num) h6
  have f15 : Gauss.gaussCost ((X.consJ j).length * (2 * X.P.kh)) (8 * X.P.ell - X.plen) ≤ X.c6 := by
    have hq2 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ hQ
    have hm : (X.consJ j).length * (2 * X.P.kh) ≤ 8 * (q + 1) ^ 2 := by
      have := Nat.mul_le_mul hc hk
      rw [Nat.one_mul] at hqq
      omega
    have hv2 : 8 * X.P.ell - X.plen ≤ 8 * (q + 1) ^ 2 := by
      have : q ≤ (q + 1) ^ 2 := by rw [sq]; exact le_trans (by omega) (Nat.le_mul_self (q + 1))
      omega
    have g := PrimAsm.SFCost.gaussCost_le _ _ _ hm hv2
    have g2 : (8 * (q + 1) ^ 2 + 1) ^ 3 ≤ (9 * (q + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have g3 : (9 * (q + 1) ^ 2) ^ 3 = 729 * (q + 1) ^ 6 := by ring
    exact fin6 (show _ ≤ 72900 * (q + 1) ^ 6 by omega) (by norm_num) hQ (by unfold capC; norm_num) h6
  have f16 : Deficit.cost (8 * X.P.ell - X.plen) ≤ X.c6 := by
    have := PrimAsm.SFCost.deficitCost_le (8 * X.P.ell - X.plen) (8 * q) hv
    rw [pow_one] at this
    exact fin6 (show _ ≤ 24 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ (by unfold capC; norm_num) h6
  have f17 : 2 * X.P.kh * (2 + 2) + 1 ≤ X.c0 :=
    fin6 (show 2 * X.P.kh * (2 + 2) + 1 ≤ 5 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ
      (by unfold capC; norm_num) h0
  have f18 : 2 * 8 + 1 ≤ X.c1 :=
    fin6 (show 2 * 8 + 1 ≤ 17 * (q + 1) ^ 0 by norm_num) (by norm_num) hQ (by unfold capC; norm_num) h1
  have f19 : coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) ≤ 2 * X.c2 + 2 := by
    have := PrimAsm.SFCost.coefCost_le (binary 8 j) (2 * X.P.kh) (X.eJ j) q (by rw [binary_length]; exact h8) hk he
    have := fin6 this (by norm_num) hQ (by unfold capC; norm_num) h2
    omega
  have f20 : 2 * X.Wt + 2 ≤ X.c4 :=
    fin6 (show 2 * X.Wt + 2 ≤ 4 * (q + 1) ^ 1 by rw [pow_one]; omega) (by norm_num) hQ (by unfold capC; norm_num) h4
  have p36 : 64 * (q + 1) ^ 3 ≤ capC * (q + 1) ^ 6 :=
    Nat.mul_le_mul (by unfold capC; norm_num) (Nat.pow_le_pow_right hQ (by norm_num))
  have f21 : ∀ k (hk : k < (X.esJ j).length), ∀ r (hr : r < (X.ents.getD (X.esJ j)[k] []).length),
      RowCaps (foldAt (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) k) (X.ents.getD (X.esJ j)[k] []) r)
        (X.ents.getD (X.esJ j)[k] [])[r] X.c0 X.c1 X.c2 X.c3 := by
    intro k hk r hr
    obtain ⟨hF1, -⟩ := hF k hk
    rw [List.getD_eq_getElem _ _ hk] at hF1
    obtain ⟨-, hF2⟩ := hF1
    obtain ⟨a1, a2, a3⟩ := hF2 r hr
    rw [List.getD_eq_getElem _ _ hr] at a2 a3
    exact rowCaps_of _ _ q _ _ _ _ a1 a2 a3 (p36.trans h0) (p36.trans h1) (p36.trans h2) (p36.trans h3)
  have f22 : ∀ k (hk : k < (X.esJ j).length),
      FetchAll.fetchCost (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) k) X.ents X.Wt (X.esJ j)[k] + 1 +
        (2 * (2 * X.Wt + 2) + 2) ≤ X.c5 := by
    intro k hk
    obtain ⟨hF1, -⟩ := hF k hk
    rw [List.getD_eq_getElem _ _ hk] at hF1
    have g := PrimAsm.SFCost.fetchCost_le _ X.ents X.Wt (X.esJ j)[k] q hW hE hF1
    have e1 : q + 1 ≤ (q + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
    exact fin6 (show _ ≤ 125 * (q + 1) ^ 5 by omega) (by norm_num) hQ (by unfold capC; norm_num) h5
  have f23 : ∀ c ∈ X.csJ j, FetchCells.tgtInnerCost c.length (binary X.TWd X.t).length ≤ X.c6 := by
    intro c hc'
    have hw := PrimT.C4Grp.hw_gen X j c hc'
    have := PrimAsm.SFCost.tgtInnerCost_le c.length (binary X.TWd X.t).length q (by omega)
      (by rw [binary_length]; exact hT)
    exact fin6 this (by norm_num) hQ (by unfold capC; norm_num) h6
  have f24 : ((List.range ((X.esJ j).length - 0)).map (fun i => FetchCells.fcCost (aOnly (X.cfJ j)) X.ents
      (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt (0 + i) + 2)).sum + 1 ≤ X.c7 := by
    have hs := PrimAsm.SFCost.sum_range_le ((X.esJ j).length - 0) (280 * (q + 1) ^ 5 + 2)
      (fun i => FetchCells.fcCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt (0 + i) + 2)
      (fun i hi => by
        obtain ⟨a, b⟩ := hF (0 + i) (by omega)
        have := PrimAsm.SFCost.fcCost_le _ X.ents (X.esJ j) (X.csJ j) (binary X.TWd X.t) X.Wt (0 + i) q hW hE a b
          (by rw [binary_length]; exact hT)
        omega)
    have h2' := mulQ (show (X.esJ j).length - 0 ≤ q + 1 by omega) (addQ 2 hQ (le_refl (280 * (q + 1) ^ 5)))
    exact fin6 (addQ 1 hQ (hs.trans h2')) (by norm_num) hQ (by unfold capC; norm_num) h7
  have f25 : Emit.emitInnerCost (exprWord V).length
      (exprWord (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length ≤ X.c0 :=
    fin6 (PrimAsm.SFCost.emitInnerCost_le _ _ q hV hA) (by norm_num) hQ (by unfold capC; norm_num) h0
  exact ⟨hm, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, hK, f14, f15, f16, f17, f18, f19, f20, f21, f22,
    f23, f24, f25⟩

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
