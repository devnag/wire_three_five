import Proof.Wire_3_5.Primitive.SeedFix.C4HBd

/-! # C4HB, part 5: the Hb printer's cell bounds (`hb_cells`)

P3:2262-2268 ("for each product and each `J_j`, the Gaussian-elimination machine counts [...]"). **`hb_cells`**
(C4HB's `HbCellsBound`): at data `D` with `DataOk D`, a prefix length `plen ≤ 2tℓ₀`, and every capacity at least
`2^32·(hbS D + 1)^8`, the Hb printer's global conditions `HbOk` hold, and at every cell its capacities `CellOk` (the
elimination block through `elimX_run`, the programs' capacities and logs) and `cellCost ≤ 2^32·(hbS D + 1)^8`.

* `elim_at`, `cellOk_at`, **`hb_cells`**.

Paper quantity of the main type: the Hb printer's per-cell step count and capacities at the call's data size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)

section Cells
variable (D : HashData) (c : HbCaps) (plen pfx : ℕ)

theorem pow_le8 (s k : ℕ) (hk : k ≤ 8) : (s + 1) ^ k ≤ (s + 1) ^ 8 := Nat.pow_le_pow_right (by omega) hk

/-- **The elimination block at a cell** (`elimX_run` at the Hb printer's capacities). -/
theorem elim_at (hplen : plen ≤ 2 * D.MP.t * D.MP.ell0) (hc : CapsGe c (2 ^ 32 * (hbS D + 1) ^ 8)) (cc : ℕ) :
    (hbX D c plen pfx).ElimOk ((hbX D c plen pfx).kOfC cc) := by
  obtain ⟨_, _, hm0, hc10, hc20, hc30, hc40, hRV0, hcL0, hcE0, hcK0, _⟩ := hc
  have hm : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).m := hm0
  have hc1 : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).c1 := hc10
  have hc2 : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).c2 := hc20
  have hc3 : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).c3 := hc30
  have hc4 : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).c4 := hc40
  have hRV : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).RV := hRV0
  have hcL : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).cL := hcL0
  have hcE : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).cE := hcE0
  have hcK : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).cK := hcK0
  clear hm0 hc10 hc20 hc30 hc40 hRV0 hcL0 hcE0 hcK0
  have hQ : 1 ≤ hbS D + 1 := by omega
  have p8 := pow_le8 (hbS D)
  have hB1 : hbS D + 1 ≤ (hbS D + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hl : (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l D
  have hT : (hbX D c plen pfx).T2 ≤ hbS D := hbS_T2 D
  have hTl : (hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ ≤ hbS D := hbS_Tl D
  have hpl2 : (hbX D c plen pfx).plen ≤ (hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ := hplen
  have hpl : (hbX D c plen pfx).plen ≤ hbS D := hpl2.trans hTl
  have hkl : (hbX D c plen pfx).kOfC cc ≤ (hbX D c plen pfx).ℓ :=
    (cell_k D c plen pfx cc).trans (Filters.MajorantParams.J_lt_ell0 D.MP).le
  have hk : (hbX D c plen pfx).kOfC cc ≤ hbS D := hkl.trans hl
  have hTk : (hbX D c plen pfx).T2 * (hbX D c plen pfx).kOfC cc ≤ hbS D := (Nat.mul_le_mul_left _ hkl).trans hTl
  have hd : (hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ - (hbX D c plen pfx).plen ≤ hbS D := by omega
  have hTl2 : (hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ ≤ (hbS D + 1) ^ 2 :=
    hTl.trans ((Nat.le_succ _).trans (q_le_q2 _))
  intro R cons stale O W P Xold g0 hR hcons hlen
  have e : SeedFix.elimCost (hbX D c plen pfx).ℓ (hbX D c plen pfx).T2 ((hbX D c plen pfx).kOfC cc)
      (hbX D c plen pfx).plen (hbX D c plen pfx).T2 = SeedFix.elimCost (hbX D c plen pfx).ℓ (hbX D c plen pfx).T2
      ((hbX D c plen pfx).kOfC cc) (hbX D c plen pfx).plen cons.length := by rw [hlen]
  rw [e]
  refine SeedFix.ElimX.elimX_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R cons stale O W P Xold g0 ?_ ?_ hkl hR hcons
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpl2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact D.MP.refCert.2.1
  · exact SeedFix.one_le_ell0 D.MP
  · -- hcap
    have := p8 8 le_rfl
    omega
  · -- hcap2
    have h1 := PrimAsm.SFCost.innerCost_le _ (hbS D) hl
    have h2 := Nat.mul_le_mul (show (hbX D c plen pfx).ℓ ≤ hbS D + 1 by omega) (Nat.add_le_add_right h1 2)
    have e1 : (hbS D + 1) * (20 * (hbS D + 1) ^ 1 + 2) = 20 * (hbS D + 1) ^ 2 + 2 * (hbS D + 1) := by ring
    have := p8 2 (by norm_num)
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcap2'
    have h1 := PrimAsm.SFCost.mulIterCost_le _ (hbS D) hl
    have h2 := Nat.mul_le_mul (show (hbX D c plen pfx).ℓ ≤ hbS D + 1 by omega) (Nat.add_le_add_right h1 2)
    have e1 : (hbS D + 1) * (24 * (hbS D + 1) ^ 1 + 2) = 24 * (hbS D + 1) ^ 2 + 2 * (hbS D + 1) := by ring
    have := p8 2 (by norm_num)
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcap2''
    have h1 := PrimAsm.SFCost.phACost_le _ (hbS D) hl
    have h2 := Nat.mul_le_mul (show (hbX D c plen pfx).plen ≤ hbS D + 1 by omega) (Nat.add_le_add_right h1 2)
    have e1 : (hbS D + 1) * (14 * (hbS D + 1) ^ 1 + 2) = 14 * (hbS D + 1) ^ 2 + 2 * (hbS D + 1) := by ring
    have := p8 2 (by norm_num)
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcap3
    have h1 := SeedFix.tableCost_le (hbX D c plen pfx).ℓ (hbX D c plen pfx).T2 (hbS D + 1) hQ (by omega) (by omega)
    have := p8 3 (by norm_num)
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcap3'
    have h1 := PrimAsm.SFCost.passesCost_le' _ _ _ (hbS D) hl hpl hTl2
    have := p8 3 (by norm_num)
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcap4
    have h1 := PrimAsm.SFCost.rowCost_le' _ _ _ (hbS D) hl hpl hTl2
    have h2 := Nat.mul_le_mul (show (hbX D c plen pfx).kOfC cc ≤ hbS D + 1 by omega) (Nat.add_le_add_right h1 2)
    have e1 : (hbS D + 1) * (140 * (hbS D + 1) ^ 3 + 2) = 140 * (hbS D + 1) ^ 4 + 2 * (hbS D + 1) := by ring
    have := p8 4 (by norm_num)
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 4 = Q4 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hm
    have : 1 ≤ (hbS D + 1) ^ 8 := Nat.one_le_pow _ _ hQ
    omega
  · -- hRV
    omega
  · -- hcL
    omega
  · -- hcapG
    omega
  · -- hcapG'
    rw [hlen]
    have h1 := PrimAsm.SFCost.gaussRowCost_le _ (hbS D) hd
    have h2 := Nat.mul_le_mul hTk (Nat.add_le_add_right h1 2)
    have e1 : hbS D * (28 * (hbS D + 1) ^ 1 + 2) ≤ 30 * (hbS D + 1) ^ 2 := by
      have : hbS D * (28 * (hbS D + 1) ^ 1 + 2) ≤ (hbS D + 1) * (30 * (hbS D + 1)) :=
        Nat.mul_le_mul (by omega) (by rw [pow_one]; omega)
      have e : (hbS D + 1) * (30 * (hbS D + 1)) = 30 * (hbS D + 1) ^ 2 := by ring
      omega
    have := p8 2 (by norm_num)
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcapG''
    rw [hlen]
    have h2 := Nat.mul_le_mul hTk (show 2 * ((hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ -
      (hbX D c plen pfx).plen) + 1 ≤ 2 * hbS D + 1 by omega)
    have e1 : hbS D * (2 * hbS D + 1) ≤ 2 * (hbS D + 1) ^ 2 := by
      have : hbS D * (2 * hbS D + 1) ≤ (hbS D + 1) * (2 * (hbS D + 1)) := Nat.mul_le_mul (by omega) (by omega)
      have e : (hbS D + 1) * (2 * (hbS D + 1)) = 2 * (hbS D + 1) ^ 2 := by ring
      omega
    have := p8 2 (by norm_num)
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcK
    omega
  · -- hcE1
    rw [hlen]
    have h1 := PrimAsm.SFCost.loopCost_le _ _ _ _ _ (hbS D) hl hT hk hpl hT
    have := p8 5 (by norm_num)
    have : 1 ≤ (hbS D + 1) ^ 5 := Nat.one_le_pow _ _ hQ
    generalize (hbS D + 1) ^ 5 = Q5 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcE2
    rw [hlen]
    have h1 := PrimAsm.SFCost.gaussCost_le _ _ (hbS D) hTk hd
    have := p8 3 (by norm_num)
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- hcE3
    have h1 := PrimAsm.SFCost.deficitCost_le _ (hbS D) hd
    rw [pow_one] at h1
    omega

end Cells

end NearCubicWires.WireExponent3_5.PrimT.C4HB
