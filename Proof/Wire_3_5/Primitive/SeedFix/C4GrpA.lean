import Proof.Wire_3_5.Primitive.SeedFix.C4Enum
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixJLink

/-! # C4.K side conditions: the structural fields of a counter value's group, generic in the child family

P3:3011-3016 (the SYM tape's entries: `R` rows per `(state, cell)`, state-major), P3:3034-3038 (the group of a valid
counter value: the eliminated system's registers, the constraint records' labels below `2^ℓ`, the fetched rows' fold
from the coefficient `±2^e`): at the enumeration context `jX P (chunk 2^{kh} n_T R batch) TWd Cap p'` of a child prefix,
every structural field of `JBody.GroupOk` holds (the modulus, the registers' invariant along the counter, `plen ≤ 8ℓ`,
the labels, the entries' count and indices, the fold's nonzero coefficients, the batch rows' `±1` coefficients, the
target words' binary layout); the capacity fields are `GroupCaps` (the side).

* `chunk_length`, `chunk_row`, `smul_ne0`, `foldl_ne0`, `fcSt_ne0`, `stAt_ok`, **`GroupCaps`**, **`groupOk_of`**.

Paper quantities of the main type: the group's fold of the fetched rows from the coefficient, at the call's entries. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Grp
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open NearCubicWires.WireExponent3_5.JoinElimination NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages JBody SplitT JEnum

/-! ## The entries -/

theorem chunk_length (N nT R : ℕ) (batch : List SExpr) : (JLink.chunk N nT R batch).length = nT * N ^ 2 := by
  simp [JLink.chunk]

theorem getD_nil_or (l : List SExpr) (i : ℕ) : l.getD i [] = [] ∨ l.getD i [] ∈ l := by
  by_cases hi : i < l.length
  · right; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · left; rw [List.getD_eq_default _ _ (by omega)]

/-- Every row of an entry is empty or a row of the batch. -/
theorem chunk_row (N nT R : ℕ) (batch : List SExpr) (e : ℕ) (V : SExpr)
    (hV : V ∈ (JLink.chunk N nT R batch).getD e []) : V = [] ∨ V ∈ batch := by
  by_cases he : e < (JLink.chunk N nT R batch).length
  · rw [List.getD_eq_getElem _ _ he] at hV
    unfold JLink.chunk at hV
    simp only [List.getElem_map, List.getElem_range, List.mem_map, List.mem_range] at hV
    obtain ⟨r, -, rfl⟩ := hV
    exact getD_nil_or batch _
  · rw [List.getD_eq_default _ _ (by omega)] at hV
    simp at hV

/-! ## The fold's coefficients stay nonzero -/

theorem smul_ne0 (V W : SExpr) (hV : ∀ a ∈ V, a.1 ≠ 0) (hW : ∀ b ∈ W, b.1 ≠ 0) : ∀ c ∈ smul V W, c.1 ≠ 0 := by
  intro c hc
  unfold smul at hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hc
  exact mul_ne_zero (hV t ht) (hW t' ht')

theorem foldl_ne0 : ∀ (rs : List SExpr) (s : FoldSt), (∀ a ∈ s.A, a.1 ≠ 0) → (∀ V ∈ rs, ∀ b ∈ V, b.1 ≠ 0) →
    ∀ a ∈ (rs.foldl FoldSt.step s).A, a.1 ≠ 0
  | [], _, hs, _ => hs
  | V :: rs, s, hs, hr => by
    rw [List.foldl_cons]
    exact foldl_ne0 rs _ (smul_ne0 s.A V hs (hr V List.mem_cons_self))
      (fun W hW => hr W (List.mem_cons_of_mem _ hW))

theorem foldAt_ne0 (s : FoldSt) (rs : List SExpr) (r : ℕ) (hs : ∀ a ∈ s.A, a.1 ≠ 0)
    (hr : ∀ V ∈ rs, ∀ b ∈ V, b.1 ≠ 0) : ∀ a ∈ (foldAt s rs r).A, a.1 ≠ 0 :=
  foldl_ne0 (rs.take r) s hs (fun V hV => hr V (List.mem_of_mem_take hV))

theorem fcSt_ne0 (ents : List (List SExpr)) :
    ∀ (L : List ℕ) (s : FoldSt), (∀ a ∈ s.A, a.1 ≠ 0) → (∀ e ∈ L, ∀ V ∈ ents.getD e [], ∀ b ∈ V, b.1 ≠ 0) →
      ∀ a ∈ (L.foldl (fun s e => foldAt s (ents.getD e []) (ents.getD e []).length) s).A, a.1 ≠ 0
  | [], _, hs, _ => hs
  | e :: L, s, hs, he => by
    rw [List.foldl_cons]
    exact fcSt_ne0 ents L _ (foldAt_ne0 s _ _ hs (he e List.mem_cons_self))
      (fun e' he' => he e' (List.mem_cons_of_mem _ he'))

theorem coefT_ne0 (bs : List Bool) (R2 e : ℕ) : ∀ a ∈ coefT bs R2 e, a.1 ≠ 0 := by
  intro a ha
  unfold coefT at ha
  rw [List.mem_singleton] at ha
  subst ha
  refine mul_ne_zero ?_ (pow_ne_zero _ two_ne_zero)
  split_ifs <;> norm_num

/-! ## The registers along the counter -/

theorem stAt_ok (X : JCtx) (S0 : JState) (h0 : S0.R.Ok X.P.ell 8) : ∀ j, (stAt X S0 j).R.Ok X.P.ell 8
  | 0 => h0
  | j + 1 => by
    have ih := stAt_ok X S0 h0 j
    show ((at_ X (tOf X j)).jNext j (stAt X S0 j)).R.Ok X.P.ell 8
    unfold JCtx.jNext
    split_ifs
    · exact regsAt_ok _ _ _ _ _ _ _ ih _
    · exact regsAt_ok _ _ _ _ _ _ _ ih _
    · exact ih

/-! ## The target words -/

theorem cellNumC_lt' {N : ℕ} (c : Cell N) : cellNumC c < N ^ 2 := by
  unfold cellNumC
  have h1 := c.1.isLt
  have h2 := c.2.isLt
  nlinarith

theorem bin_split (a b x t : ℕ) (hx : x < 2 ^ a) : binary (a + b) (x + 2 ^ a * t) = binary a x ++ binary b t := by
  rw [Split.binary_add_split]
  congr 1
  · rw [← Cells.binary_mod a (x + 2 ^ a * t), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem bin_split' (a b x t N2 : ℕ) (hN : N2 = 2 ^ a) (hx : x < N2) :
    binary (a + b) (x + N2 * t) = binary a x ++ binary b t := by
  subst hN; exact bin_split a b x t hx

/-- The target word of a fetched entry is its cell word, then the state word. -/
theorem hcs_gen (X : JCtx) (j : ℕ) : ∀ k (_hk : k < (X.esJ j).length) (hk' : k < (X.csJ j).length),
    binary X.Wt (X.esJ j)[k] = (X.csJ j)[k] ++ binary X.TWd X.t := by
  intro k _ _
  have hN : X.P.N ^ 2 = 2 ^ (2 * X.P.kh) := by
    show (2 ^ X.P.kh) ^ 2 = 2 ^ (2 * X.P.kh)
    rw [← pow_mul, Nat.mul_comm]
  simp only [JCtx.esJ, JCtx.csJ, List.getElem_map, List.getElem_finRange, JCtx.Wt]
  unfold Cells.cellW
  exact bin_split' _ _ _ _ _ hN (cellNumC_lt' _)

theorem hw_gen (X : JCtx) (j : ℕ) : ∀ c ∈ X.csJ j, c.length + (binary X.TWd X.t).length = X.Wt := by
  intro c hc
  simp only [JCtx.csJ, List.mem_map] at hc
  obtain ⟨k, -, rfl⟩ := hc
  simp [Cells.cellW, JCtx.Wt]

/-! ## The capacity fields (the side) and the group's hypotheses -/

/-- **The capacity fields of a group**: `GroupOk`'s numeric fields and `FcOk`'s capacity fields. -/
structure GroupCaps (X : JCtx) (j : ℕ) (S : JState) (V : SExpr) : Prop where
  hm : 1 ≤ X.m
  hkc : consInnerCost 8 X.P.ell (2 * X.P.kh) ≤ X.c0
  hcap : 2 * X.P.ell + 2 ≤ X.c0
  hcap2 : X.P.ell * (innerCost X.P.ell + 2) + 1 ≤ X.c1
  hcap2' : X.P.ell * (mulIterCost X.P.ell + 2) + 1 ≤ X.c1
  hcap2'' : X.plen * (phACost X.P.ell + 2) + 1 ≤ X.c1
  hcap3 : tableCost X.P.ell 8 ≤ X.c2
  hcap3' : passesCost X.P.ell X.plen (8 * X.P.ell) ≤ X.c2
  hcap4 : 2 * X.P.kh * (rowCost X.P.ell X.plen (8 * X.P.ell) + 2) + 1 ≤ X.c4
  hRV : 2 * X.P.ell + 1 ≤ X.c3
  hcL : 2 * X.P.ell + 1 ≤ X.c5
  hcapG : 2 * (8 * X.P.ell - X.plen) + 13 ≤ X.c0
  hcapG' : (X.consJ j).length * (2 * X.P.kh) * (Gauss.rowCost (8 * X.P.ell - X.plen) + 2) + 3 ≤ X.c1
  hcapG'' : (X.consJ j).length * (2 * X.P.kh) * (2 * (8 * X.P.ell - X.plen) + 1) + 1 ≤ X.c1
  hcK : 8 * X.P.ell - X.plen ≤ X.cK
  hcE1 : loopCost X.P.ell 8 (2 * X.P.kh) X.plen (X.consJ j).length + 1 + 1 ≤ X.c6
  hcE2 : Gauss.gaussCost ((X.consJ j).length * (2 * X.P.kh)) (8 * X.P.ell - X.plen) ≤ X.c6
  hcE3 : Deficit.cost (8 * X.P.ell - X.plen) ≤ X.c6
  hcf0 : 2 * X.P.kh * (2 + 2) + 1 ≤ X.c0
  hcf1 : 2 * 8 + 1 ≤ X.c1
  hcf2 : coefCost (binary 8 j) (2 * X.P.kh) (X.eJ j) ≤ 2 * X.c2 + 2
  fcE : 2 * X.Wt + 2 ≤ X.c4
  fcRows : ∀ k (hk : k < (X.esJ j).length), ∀ r (hr : r < (X.ents.getD (X.esJ j)[k] []).length),
    RowCaps (foldAt (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) k) (X.ents.getD (X.esJ j)[k] []) r)
      (X.ents.getD (X.esJ j)[k] [])[r] X.c0 X.c1 X.c2 X.c3
  fcF : ∀ k (hk : k < (X.esJ j).length),
    fetchCost (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) k) X.ents X.Wt (X.esJ j)[k] + 1 + (2 * (2 * X.Wt + 2) + 2) ≤ X.c5
  hcG : ∀ c ∈ X.csJ j, tgtInnerCost c.length (binary X.TWd X.t).length ≤ X.c6
  hcH : ((List.range ((X.esJ j).length - 0)).map (fun i => fcCost (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.csJ j)
    (binary X.TWd X.t) X.Wt (0 + i) + 2)).sum + 1 ≤ X.c7
  hcE : emitInnerCost (exprWord V).length
    (exprWord (fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length ≤ X.c0

section Group
variable (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (TWd Cap : ℕ) (p' : List Bool)


/-- **The group's structural fields at the call's entries**: with the capacity fields, the group's hypotheses. -/
theorem groupOk_of (hplen : p'.length ≤ 8 * P.ell) (hnT : nT ≤ 2 ^ TWd)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (j : ℕ)
    (hj : j < nT * 2 ^ (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p').w)
    (hcap : GroupCaps (at_ (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p')
      (tOf (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j)) j
      (stAt (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') (C4Enum.S0 P) j)
      (outAt (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j)) :
    GroupOk (at_ (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p')
      (tOf (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j)) j
      (stAt (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') (C4Enum.S0 P) j)
      (outAt (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j) := by
  set X := C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p' with hX
  set t := tOf X j with ht
  have htn : t < nT := by
    rw [ht]; unfold tOf
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
  have hN2 : (2 ^ P.kh) ^ 2 = 2 ^ (2 * P.kh) := by rw [← pow_mul, Nat.mul_comm]
  have hlen : (at_ X t).ents.length = nT * (2 ^ P.kh) ^ 2 := chunk_length _ _ _ _
  have hes : ∀ e ∈ (at_ X t).esJ j, e < (at_ X t).ents.length := by
    intro e he
    simp only [JCtx.esJ, List.mem_map] at he
    obtain ⟨k, -, rfl⟩ := he
    rw [hlen]
    have h1 := cellNumC_lt' (Shared.cellOf (by norm_num) (wOf P j) k)
    show cellNumC (cellOf (by norm_num) (wOf P j) k) + (2 ^ P.kh) ^ 2 * t < nT * (2 ^ P.kh) ^ 2
    nlinarith
  refine ⟨P.cert.2.1, stAt_ok X (C4Enum.S0 P) (C4Enum.S0_ok P) j, hcap.hm, hplen, ?_, hcap.hkc, hcap.hcap,
    hcap.hcap2, hcap.hcap2', hcap.hcap2'', hcap.hcap3, hcap.hcap3', hcap.hcap4, hcap.hRV, hcap.hcL, hcap.hcapG,
    hcap.hcapG', hcap.hcapG'', hcap.hcK, hcap.hcE1, hcap.hcE2, hcap.hcE3, hcap.hcf0, hcap.hcf1, hcap.hcf2,
    ⟨?_, hes, hcap.fcE, ?_, ?_, hcap.fcRows, hcap.fcF⟩, ?_, ?_, hcap.hcG, hcap.hcH, hcap.hcE⟩
  · -- the constraint records' labels
    intro con hcon
    simp only [JCtx.consJ, consL, List.mem_filterMap] at hcon
    obtain ⟨k, -, hk⟩ := hcon
    split_ifs at hk
    · cases hk
      exact Nat.mod_lt _ (by positivity)
  · -- the entries fit the target width
    rw [hlen, hN2]
    show nT * 2 ^ (2 * P.kh) ≤ 2 ^ (2 * P.kh + TWd)
    rw [pow_add, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (le_trans hnT (le_refl _))
  · -- the fold's coefficients are nonzero
    intro k _ a ha
    exact fcSt_ne0 _ _ _ (coefT_ne0 _ _ _)
      (fun e _ V hV b hb => by
        rcases chunk_row _ _ _ _ _ _ hV with h | h
        · subst h; simp at hb
        · rcases hpm V h b hb with h1 | h1 <;> rw [h1] <;> norm_num) a ha
  · -- the batch rows' coefficients are `±1`
    intro e _ V hV b hb
    rcases chunk_row _ _ _ _ _ _ hV with h | h
    · subst h; simp at hb
    · exact hpm V h b hb
  · exact hcs_gen _ j
  · exact hw_gen _ j

end Group

end NearCubicWires.WireExponent3_5.PrimT.C4Grp
