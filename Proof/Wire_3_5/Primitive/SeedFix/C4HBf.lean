import Proof.Wire_3_5.Primitive.SeedFix.C4HBe

/-! # C4HB, part 6: `hb_cells`

P3:2262-2268. **`hb_cells`** (C4HB's `HbCellsBound`): at data `D` with `DataOk D`, `plen ≤ 2tℓ₀`, and every
capacity at least `2^32·(hbS D + 1)^8`: the Hb printer's `HbOk`, and at every cell `CellOk` (`elim_at` and the
programs' capacities and logs) and `cellCost ≤ 2^32·(hbS D + 1)^8`.

* `cellOk_at`, **`hb_cells`**.

Paper quantity of the main type: the Hb printer's per-cell step count and capacities at the call's data size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.RepairOrdinary

section Cells
variable (D : HashData) (hD : DataOk D) (c : HbCaps) (plen pfx : ℕ)
include hD

/-- **A cell's capacities** at the data size. -/
theorem cellOk_at (hplen : plen ≤ 2 * D.MP.t * D.MP.ell0) (hc : CapsGe c (2 ^ 32 * (hbS D + 1) ^ 8)) (cc : ℕ)
    (hcc : cc < (hbX D c plen pfx).n) : (hbX D c plen pfx).CellOk cc := by
  have hel := elim_at D c plen pfx hplen hc cc
  obtain ⟨hcap0, hcapL0, _⟩ := hc
  have hcap : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).cap := hcap0
  have hcapL : 2 ^ 32 * (hbS D + 1) ^ 8 ≤ (hbX D c plen pfx).capL := hcapL0
  clear hcap0 hcapL0
  have hQ : 1 ≤ hbS D + 1 := by omega
  have hB1 : hbS D + 1 ≤ (hbS D + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have p2 := pow_le8 (hbS D) 2 (by norm_num)
  have p3 := pow_le8 (hbS D) 3 (by norm_num)
  have p4 := pow_le8 (hbS D) 4 (by norm_num)
  have hl : (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l D
  have hT : (hbX D c plen pfx).T2 ≤ hbS D := hbS_T2 D
  have hJ : (hbX D c plen pfx).J ≤ hbS D := hbS_J D
  have hA : 2 ^ ((hbX D c plen pfx).ℓ + 1) ≤ hbS D := hbS_l2 D
  have hpw : (popsWord (hbX D c plen pfx).pops).length ≤ hbS D := hbS_pw D
  have hwt : (wtWord (hbX D c plen pfx).Ws).length ≤ hbS D := hbS_wt D
  have hht : (htWord (hbX D c plen pfx).Fs).length ≤ hbS D := hbS_ht D
  have hG : (hbX D c plen pfx).G ≤ hbS D := hbS_G D
  have hnE : (hbX D c plen pfx).nE ≤ hbS D := hbS_nE D
  have hlam : (hbX D c plen pfx).lamOf cc ≤ hbS D := (cell_lam D c plen pfx cc).trans (hbS_J D)
  have hp : (hbX D c plen pfx).pOf cc ≤ hbS D := ((cell_p D c plen pfx cc hcc).trans_le (hbS_P D)).le
  have he : (hbX D c plen pfx).eOf cc ≤ hbS D := ((cell_e D c plen pfx cc hcc).trans_le (hbS_nE D)).le
  have hq : (hbX D c plen pfx).qOf cc ≤ hbS D := ((cell_q D c plen pfx cc hcc).trans_le (hbS_N2 D)).le
  have hx : (hbX D c plen pfx).xOf cc ≤ hbS D := (cell_x D c plen pfx cc).trans (hbS_Tl D)
  refine ⟨hel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- capV
    omega
  · -- capC
    omega
  · -- capS
    unfold ldSum
    omega
  · -- capT1
    omega
  · -- capT2
    have hmr := monoRoom_le (4 * (hbX D c plen pfx).qOf cc) (hbX D c plen pfx).G (hbS D) (by omega) hG
    have m1 : (hbX D c plen pfx).T2 * (10 * monoRoom (4 * (hbX D c plen pfx).qOf cc) (hbX D c plen pfx).G
        (hbX D c plen pfx).G + 2) ≤ (hbS D + 1) * (1062 * (hbS D + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 2 (hbS D + 1) hQ; omega)
    have e1 : (hbS D + 1) * (1062 * (hbS D + 1) ^ 2) = 1062 * (hbS D + 1) ^ 3 := by ring
    have m2 : (hbX D c plen pfx).qOf cc * (hbX D c plen pfx).nE ≤ (hbS D + 1) * (hbS D + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e2 : (hbS D + 1) * (hbS D + 1) = (hbS D + 1) ^ 2 := by ring
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 4 = Q4 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- capT3
    have := tb_le D hD c plen pfx cc hcc
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- logV
    have := valBound_at D c plen pfx cc hcc
    generalize (hbS D + 1) ^ 3 = Q3 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- logC
    have := consBound_at D c plen pfx cc
    generalize (hbS D + 1) ^ 2 = Q2 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- logT
    have := tcB_at D hD c plen pfx cc hcc
    generalize (hbS D + 1) ^ 4 = Q4 at *
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega
  · -- logA
    have := advB_at D c plen pfx
    generalize (hbS D + 1) ^ 8 = Q8 at *
    omega

end Cells

/-- **The Hb printer's cell bounds** (C4HB's `HbCellsBound`). -/
theorem hb_cells : HbCellsBound := by
  intro D hD c plen pfx hplen hc
  refine ⟨?_, fun cc hcc => ⟨cellOk_at D hD c plen pfx hplen hc cc hcc, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, hD.hF, hD.hG, ?_⟩
    · show 1 ≤ 2 * D.MP.t
      have := hD.ht
      omega
    · exact (Filters.MajorantParams.J_lt_ell0 D.MP).le
    · show (wsOf D.MP).length = D.MP.J + 1
      simp [wsOf]
    · show 1 ≤ c.cap
      have := hc.1
      have : 1 ≤ (hbS D + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
      omega
  · exact le_big _ _ _ _ (cellCost_at D hD c plen pfx cc hcc hplen) (by norm_num) (by norm_num) (by omega)

end NearCubicWires.WireExponent3_5.PrimT.C4HB
