import Proof.Wire_3_5.FinalPass.EnumCap1
import Proof.Wire_3_5.Primitive.SeedFix.C4EnumDock

/-! # The enumeration's side conditions at a call, generic in the batch, part 2: `EnumOk`

P3:3011-3016 (`samp:seed`'s enumeration of the cells at a child prefix `p'`). For the call's seed parameters `P`,
entry count `n_T`, rows per entry `R` and `±1`-coefficient batch, with `Q ≥ qG(8ℓ)` (the group size bound at the
longest prefix), every capacity `Cap ≥ capC·(Q+1)^6` and the cell cost bound `K ≥ 6000·(Q+1)^6`: the enumeration's
hypotheses `C4Dock.EnumOk` hold at every child prefix. Mode-generic (SYM, THR and HASH are instances): the only
mode facts are `1 ≤ Q_P`, `n_T ≤ 2^{TWd}` and the bound `Q`.

* `cellOk_of`, `splitOk_of` (from `Cap ≥ 2000(q+1)²`), `qG_mono`, **`enumOk_of`**.

Paper quantity of the main type: the enumeration's hypotheses at a call's child prefix. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler

/-- **The cells' capacities** from `Cap ≥ 2000(q+1)²`. -/
theorem cellOk_of (P : SeedParams) (ents : List (List SExpr)) (TWd Cap : ℕ) (p' : List Bool) (q : ℕ)
    (hl : P.ell ≤ q) (hk : P.kh ≤ q) (h8 : 8 ≤ q) (hCap : 2000 * (q + 1) ^ 2 ≤ Cap) :
    JBody.CellOk (PrimT.C4Enum.jX P ents TWd Cap p') := by
  have f1 := PrimAsm.SFCost.fieldCost_le P.ell q hl
  have f2 := PrimAsm.SFCost.fieldCost_le P.kh q hk
  have s1 := PrimAsm.SFCost.splitFieldsCost_le P.ell P.kh q hl hk
  have s2 := PrimAsm.SFCost.splitRotCost_le P.kh q hk
  have c1 := PrimAsm.SFCost.cellsInnerCost_le P.kh q hk
  have v1 := PrimAsm.SFCost.validInnerCost_le 8 P.ell q h8 hl
  have hq : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  simp only [pow_one] at f1 f2 s1 s2 c1
  generalize (q + 1) ^ 2 = Q2 at hCap v1 hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [PrimT.C4Enum.jX] <;>
    first | omega | (simp; omega)

/-- **The split's capacities** from `Cap ≥ 2000(q+1)²` (with `TWd ≤ q`). -/
theorem splitOk_of (P : SeedParams) (ents : List (List SExpr)) (TWd Cap : ℕ) (p' : List Bool) (q : ℕ)
    (hl : P.ell ≤ q) (hk : P.kh ≤ q) (ht : TWd ≤ q) (hCap : 2000 * (q + 1) ^ 2 ≤ Cap) :
    JEnum.SplitOk (PrimT.C4Enum.jX P ents TWd Cap p') := by
  have f3 := PrimAsm.SFCost.fieldCost_le TWd q ht
  have s1 := PrimAsm.SFCost.splitFieldsCost_le P.ell P.kh q hl hk
  have s2 := PrimAsm.SFCost.splitRotCost_le P.kh q hk
  have hq : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  simp only [pow_one] at f3 s1 s2
  generalize (q + 1) ^ 2 = Q2 at hCap hq
  refine ⟨?_, ?_⟩ <;> simp only [PrimT.C4Enum.jX] <;> omega

/-- `qG` is monotone in the prefix length. -/
theorem qG_mono (P : SeedParams) (nT R b TWd a a' : ℕ) (h : a ≤ a') :
    PrimT.C4Grp.qG P nT R b TWd a ≤ PrimT.C4Grp.qG P nT R b TWd a' := by
  unfold PrimT.C4Grp.qG
  omega

/-- The call's numbers below `qG`. -/
theorem nums_le_qG (P : SeedParams) (nT R b TWd a : ℕ) :
    8 * P.ell + 2 * P.kh + TWd + 8 ≤ PrimT.C4Grp.qG P nT R b TWd a := by
  unfold PrimT.C4Grp.qG
  omega

/-- **The enumeration's hypotheses at every child prefix**, generic in the batch: `Q ≥ qG(8ℓ)`,
`Cap ≥ capC·(Q+1)^6`, `K ≥ 6000·(Q+1)^6`. -/
theorem enumOk_of (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (TWd Cap K Q : ℕ)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (hQ1 : 1 ≤ P.Q) (hnT : nT ≤ 2 ^ TWd)
    (hq : PrimT.C4Grp.qG P nT R (PrimT.C4Grp.bsz batch) TWd (8 * P.ell) ≤ Q)
    (hCap : capC * (Q + 1) ^ 6 ≤ Cap) (hK : 6000 * (Q + 1) ^ 6 ≤ K) (p : List Bool) (b : Bool)
    (hp : p.length < 8 * P.ell) :
    PrimT.C4Dock.EnumOk P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap nT R K batch (p ++ [b]) := by
  have hplen : (p ++ [b]).length ≤ 8 * P.ell := by
    rw [List.length_append, List.length_singleton]; omega
  obtain ⟨q, hqd⟩ : ∃ q, q = PrimT.C4Grp.qG P nT R (PrimT.C4Grp.bsz batch) TWd (p ++ [b]).length := ⟨_, rfl⟩
  have hqQ : q ≤ Q := by
    rw [hqd]; exact (qG_mono P nT R _ TWd _ _ hplen).trans hq
  have hn := nums_le_qG P nT R (PrimT.C4Grp.bsz batch) TWd (8 * P.ell)
  have hQ6 : (q + 1) ^ 6 ≤ (Q + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hq6 : capC * (q + 1) ^ 6 ≤ Cap := (Nat.mul_le_mul_left _ hQ6).trans hCap
  have h26 : 2000 * (Q + 1) ^ 2 ≤ Cap := by
    have : (Q + 1) ^ 2 ≤ (Q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : 2000 * (Q + 1) ^ 2 ≤ capC * (Q + 1) ^ 6 := Nat.mul_le_mul (by unfold capC; norm_num) this
    omega
  refine ⟨JLink.chunk_ok _ _ _ _, hQ1, hnT, cellOk_of P _ TWd Cap _ Q (by omega) (by omega) (by omega) h26,
    splitOk_of P _ TWd Cap _ Q (by omega) (by omega) (by omega) h26, ?_, ?_⟩
  · intro j hj
    have hg := PrimT.C4Grp.groupSmall_of P nT R batch TWd Cap (p ++ [b]) hpm hplen j hj
    rw [← hqd] at hg
    have hw := PrimT.C4Grp.wT_le_qG P (JLink.chunk (2 ^ P.kh) nT R batch) nT R TWd Cap (p ++ [b])
      (PrimT.C4Grp.bsz batch) (PrimT.C4Grp.bsz_pos batch)
    rw [← hqd] at hw
    have hkh : P.kh ≤ q := by
      have := nums_le_qG P nT R (PrimT.C4Grp.bsz batch) TWd (p ++ [b]).length
      rw [← hqd] at this; omega
    have hc := PrimAsm.SFCost.cellCost_le _ j _ q hg hkh hw
    have : 6000 * (q + 1) ^ 6 ≤ 6000 * (Q + 1) ^ 6 := Nat.mul_le_mul_left _ hQ6
    omega
  · intro j hj _
    have hg := PrimT.C4Grp.groupSmall_of P nT R batch TWd Cap (p ++ [b]) hpm hplen j hj
    rw [← hqd] at hg
    exact PrimT.C4Grp.groupOk_of P nT R batch TWd Cap (p ++ [b]) hplen hnT hpm j hj
      (groupCaps_small _ j _ _ q hg (show 1 ≤ Cap by
          have : 1 ≤ capC * (q + 1) ^ 6 := Nat.mul_pos (by unfold capC; norm_num) (Nat.one_le_pow _ _ (by omega))
          omega)
        (show 8 * P.ell - (p ++ [b]).length ≤ 8 * P.ell by omega) hq6 hq6 hq6 hq6 hq6 hq6 hq6 hq6)

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
