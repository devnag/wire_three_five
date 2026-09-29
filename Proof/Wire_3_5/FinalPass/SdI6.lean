import Proof.Wire_3_5.FinalPass.SdI5

/-! # S4 (the seeds phase), part 55: the step counts below powers of the sizes' bound (P3:3170-3178)

At the sizes below `X` (`AtomsX`): one point's steps **`ptB_X`** `≤ 23000·X⁴` (the per-point cost, `ptB_le`), one
seed's own steps **`tabB_X`** `≤ 10⁵·X³` (the tables' word, the two tables copied, the row counter), the prep
**`prep_X`** `≤ 10⁴·X²`, the body's fixed steps **`bodyA_le`** `≤ (2400 + 3·nn)·(cap + 1)`.

Paper quantity of the main type: the seeds phase's running time's three parts (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL)
open NearCubicWires.SupplierWalk (majorityThreshold)

section Costs
variable (P : StarParams) (carriers : List (Carrier P.n)) (FP : GapParams) (X : ℕ)

/-- **One point's steps** at the sizes' bound. -/
theorem ptB_X (H : AtomsX P carriers FP X) (nE Vm T : ℕ) (hnE : nE ≤ X) (hV : Vm ≤ X) (hT : T ≤ X)
    (e : GapSeed FP) :
    ptB FP P carriers P.s P.b (P.r / 2) (P.n - P.r * P.b) nE Vm T e ≤ 23000 * (X * X * X * X) := by
  obtain ⟨hb, hs, hr, h2s, hhL, hdRow, hdR, h1, h2, hsr⟩ := star_le P
  have hn := H.n2
  have hsh : P.s * (P.r / 2) ≤ X * X := hsr.trans (Nat.mul_le_mul (by omega) (by omega))
  have hthr : majorityThreshold FP.walkLen ≤ X := by
    have := thr_le FP; have := walkLen_le FP; have := H.err; omega
  exact ptB_le FP P carriers P.s P.b (P.r / 2) (P.n - P.r * P.b) nE Vm T e (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hsh hnE hV hT (by omega) (by omega)
    (fun k hk => ⟨H.tabH k hk, H.mask k hk, H.tbl e k hk, hthr⟩)

theorem tb_X (H : AtomsX P carriers FP X) (e : GapSeed FP) (k : ℕ) :
    (tb FP e (Seams.carLen carriers k)).length ≤ 258 * X + 256 * (X * X) + 1 := by
  unfold tb
  rw [TabW.tw_len]
  have hw : FP.walkLen ≤ X := by have := walkLen_le FP; have := H.err; omega
  have := Nat.mul_le_mul hw (show 2 + 128 * (2 * Seams.carLen carriers k + 2) ≤ 258 + 256 * X by
    have := H.cl k; omega)
  have e1 : X * (258 + 256 * X) = 258 * X + 256 * (X * X) := by ring
  omega

/-- **One seed's own steps** at the sizes' bound. -/
theorem tabB_X (H : AtomsX P carriers FP X) (e : GapSeed FP) :
    tabB FP P carriers (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length e ≤
      100000 * (X * X * X) := by
  have hw := twW_le P carriers FP X H
  have t0 := tb_X P carriers FP X H e 0
  have t1 := tb_X P carriers FP X H e 1
  obtain ⟨hb, hs, hr, h2s, hhL, hdRow, hdR, h1, h2, hsr⟩ := star_le P
  have hn := H.n2
  have hx2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hx3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have hx2' : 2 * (X * X) ≤ X * X * X := by
    have := Nat.mul_le_mul_left (X * X) (show 2 ≤ X by omega); linarith
  have hx1' : 2 * X ≤ X * X := by
    have := Nat.mul_le_mul_left X (show 2 ≤ X by omega); linarith
  unfold tabB
  unfold cpCost
  generalize (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length = Lw at hw ⊢
  generalize (tb FP e (Seams.carLen carriers 0)).length = a0 at t0 ⊢
  generalize (tb FP e (Seams.carLen carriers 1)).length = a1 at t1 ⊢
  generalize X * X * X = x3 at hw hx3 hx2' ⊢
  generalize X * X = x2 at t0 t1 hx2 hx3 hx2' hx1' ⊢
  omega

/-- **The prep's steps** at the sizes' bound. -/
theorem prep_X (H : AtomsX P carriers FP X) : prepCost (Seams.s4Small2 P carriers FP) ≤ 10000 * (X * X) := by
  have hv := vs_le P carriers FP X H
  have hul := ul_le X _ hv
  have hlen : (Seams.s4Small2 P carriers FP).length = 16 := rfl
  rw [hlen] at hul
  have hn := H.n2
  have hreq := TabW.reqT_le P.n FP.len FP.cap FP.errExp (Seams.carLen carriers 0) (Seams.carLen carriers 1)
    (Fintype.card (GapSeed FP)) X hn H.len H.cap (by have := H.err; omega) (H.cl 0) (H.cl 1) H.G
  have g1 := getD_le X _ hv 1
  have g3 := getD_le X _ hv 3
  have g6 := getD_le X _ hv 6
  have g11 := getD_le X _ hv 11
  have hG : 2 ^ (Seams.s4Small2 P carriers FP).getD 11 0 ≤ X := by rw [nE_s4]; exact H.G
  have hbl : natBitLength P.n ≤ P.n + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have p1 := Nat.mul_le_mul g1 (show 18 * (Seams.s4Small2 P carriers FP).getD 3 0 + 8 ≤ 18 * X + 8 by omega)
  have p2 := Nat.mul_le_mul g11 (show 18 * 2 ^ (Seams.s4Small2 P carriers FP).getD 11 0 + 7 ≤ 18 * X + 7 by omega)
  have p3 := Nat.mul_le_mul (show natBitLength P.n + 10 ≤ X + 11 by omega) (show 100 * P.n + 200 ≤ 100 * X + 200 by omega)
  have e1 : X * (18 * X + 8) = 18 * (X * X) + 8 * X := by ring
  have e2 : X * (18 * X + 7) = 18 * (X * X) + 7 * X := by ring
  have e3 : (X + 11) * (100 * X + 200) = 100 * (X * X) + 1300 * X + 2200 := by ring
  have hx1' : 2 * X ≤ X * X := by
    have := Nat.mul_le_mul_left X (show 2 ≤ X by omega); linarith
  unfold prepCost reqCost
  rw [ppN_s4, ppReq_s4]
  generalize X * X = x2 at e1 e2 e3 hx1' ⊢
  omega

/-- **The body's fixed steps.** -/
theorem bodyA_le (cap nn : ℕ) : bodyA cap nn ≤ (2400 + 3 * nn) * (cap + 1) := by
  unfold bodyA tdCost
  have e : (2400 + 3 * nn) * (cap + 1) = 2400 * cap + 2400 + 3 * (nn * cap) + 3 * nn := by ring
  have e2 : nn * (3 * cap + 2) = 3 * (nn * cap) + 2 * nn := by ring
  rw [e, e2]
  omega

end Costs

end NearCubicWires.WireExponent3_5.FinalPass.Sd

