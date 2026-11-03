import Proof.Wire_3_5.FinalPass.SdQ3
import Proof.Wire_3_5.FinalPass.SdEvC

/-! # S4 (the seeds phase), part 38: the body's run, its pieces (P3:3170-3178)

* **`QNum`**: the seed loop's numeric hypotheses at a star call (the capacity against the star parameters, the
  counter width `T`, the sample, the carriers' mask capacities, the tables word, the per-point values' bound);
* **`setRS_cost_le`**: the setup's steps within `2300·(cap + 1)`; `setROut_sRp`, `setROut_le`;
* `keptC_of` (a kept stream by its index), `kh_pos` (`1 ≤ s·(r/2)`), `n_split` (`(r/2)b + (r/2)b + (n − rb) = n`).

Paper quantity of the main type: the seeds phase's numeric side conditions and its setup's running time. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)
open NearCubicWires.SupplierWalk (majorityThreshold)

theorem kh_pos (P : StarParams) : 1 ≤ P.s * (P.r / 2) := by
  have hr := P.two_le_r
  have h4 := P.four_r_le_n
  have hq : 4 ≤ P.n / P.r := (Nat.le_div_iff_mul_le P.r_pos).mpr (by omega)
  have hs : 0 < P.s := Nat.log_pos (by norm_num) (by omega)
  have hh : 1 ≤ P.r / 2 := by omega
  exact Nat.mul_le_mul hs hh

theorem n_split (P : StarParams) : P.r / 2 * P.b + P.r / 2 * P.b + (P.n - P.r * P.b) = P.n := by
  have hre : P.r / 2 * 2 = P.r := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  have hhb : P.r / 2 * P.b + P.r / 2 * P.b = P.r * P.b := by rw [← two_mul, ← mul_assoc, mul_comm 2, hre]
  have hrb := P.r_mul_b_le
  omega

/-- **The seed loop's numeric hypotheses** at a star call. -/
structure QNum (cap : ℕ) (FP : GapParams) (P : StarParams) (carriers : List (Stars.Carrier P.n)) {N : ℕ}
    (ps : List (Fin N × Fin N)) (T Vm tw : ℕ) : Prop where
  c2 : 2 ≤ cap
  capT : 2 * T + 2 < cap
  cs : 2 * 2 ^ P.s ≤ cap ∧ P.s ≤ cap ∧ 2 * P.n ≤ cap ∧ P.b ≤ cap ∧ P.r / 2 ≤ cap ∧ P.n - P.r * P.b ≤ cap
  p : ps.length * (2 * (2 * (P.s * (P.r / 2)) + 1)) ≤ cap
  c8 : 8 * (P.n + 2) ≤ cap
  dT : dR P ≤ T ∧ dRow P ≤ T
  cc2 : 2 * dR P + 1 ≤ cap ∧ 2 * dRow P + 1 ≤ cap
  mkc : ∀ (e : GapSeed FP) (k : Fin 2) (hk : k.val < carriers.length),
    MkCap cap (PrimT.tabH (carriers.get ⟨k.val, hk⟩)) P.n (maskGates (carriers.get ⟨k.val, hk⟩)).length
      (filterTable FP e (maskGates (carriers.get ⟨k.val, hk⟩)).length) (majorityThreshold FP.walkLen)
  twc : tw + 1 < cap
  Vc : Vm ≤ cap

section Body
variable {nw nn nsc nrs : ℕ}

theorem keptC_of (i : Fin (bns nw nsc + 1)) (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) (h2 : i.val ≠ 2) (h3 : i.val ≠ 3)
    (h4 : i.val < 10 ∨ 25 ≤ i.val) (h5 : i.val ≠ 25) (h6 : i.val ≠ 26) (h7 : i.val < 47 + nw) : KeptC i := by
  refine ⟨⟨ne_of_val (show i.val ≠ 0 from h0), ne_of_val (show i.val ≠ 2 from h2), ne_of_val (show i.val ≠ 3 from h3),
    fun k => ⟨?_, ?_, ?_⟩, ?_⟩, ne_of_val (show i.val ≠ 1 from h1), ne_of_val (show i.val ≠ 25 from h5),
    ne_of_val (show i.val ≠ 26 from h6)⟩
  · have := k.isLt; exact ne_of_val (show i.val ≠ 10 + 4 * k.val by omega)
  · have := k.isLt; exact ne_of_val (show i.val ≠ 11 + 4 * k.val by omega)
  · have := k.isLt; exact ne_of_val (show i.val ≠ 12 + 4 * k.val by omega)
  · unfold IsSc; omega

theorem setROut_sRp (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 30) :
    (setROut σ H0 H1 T0 T1).val (sRp k) = σ.val (sRp k) :=
  setROut_lo σ H0 H1 T0 T1 (sRp k) (show 10 + k.val < 44 by omega)

theorem sJobs_v (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 cap : ℕ) (hv : ∀ k : Fin 30, σ.val (sRp k) ≤ cap)
    (hH0 : H0 ≤ cap) (hH1 : H1 ≤ cap) (hT0 : T0 ≤ cap) (hT1 : T1 ≤ cap) :
    ∀ j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))), (setROut σ H0 H1 T0 T1).val j.v ≤ cap := by
  intro j hj
  simp only [sJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only <;>
    first
      | (rw [setROut_sRp]; exact hv _)
      | (rw [setROut_sH]; simp; omega)
      | (rw [setROut_sTT]; simp; omega)

theorem sClr_v (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 cap : ℕ) (hv : ∀ k : Fin 30, σ.val (sRp k) ≤ cap)
    (hH0 : H0 ≤ cap) (hH1 : H1 ≤ cap) (hT0 : T0 ≤ cap) (hT1 : T1 ≤ cap) :
    ∀ q ∈ (sClr : List (Fin (bnr nn nrs))), (setROut σ H0 H1 T0 T1).val q ≤ cap := by
  intro q hq
  simp only [sClr, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (rw [setROut_sRp]; exact hv _)
      | (rw [setROut_sH]; simp; omega)
      | (rw [setROut_sTT]; simp; omega)

theorem setRS_cost_le (cap : ℕ) (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (hv : ∀ k : Fin 30, σ.val (sRp k) ≤ cap)
    (hH0 : H0 ≤ cap) (hH1 : H1 ≤ cap) (hT0 : T0 ≤ cap) (hT1 : T1 ≤ cap) :
    setRCost σ H0 H1 T0 T1 + (flJobsCost (setROut σ H0 H1 T0 T1) sJobs + 1 +
      (1 + 1 + (sClr.map fun r => 3 * (setROut σ H0 H1 T0 T1).val r + 2).sum)) + 1 ≤ 2300 * (cap + 1) := by
  have c1 : cpjCost σ cps ≤ 9 * (18 * cap + 4) := by
    have := lsum_le (cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs))) (fun p => 18 * σ.val p.1 + 3 + 1)
      (18 * cap + 4) (fun p hp => by
        simp only [cps, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | (have h := hv 1; dsimp only; omega)
            | (have h := hv 2; dsimp only; omega)
            | (have h := hv 3; dsimp only; omega)
            | (have h := hv 4; dsimp only; omega)
            | (have h := hv 5; dsimp only; omega)
            | (have h := hv 6; dsimp only; omega))
    have hl : (cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs))).length = 9 := rfl
    rw [hl] at this
    exact this
  have c2 := hv 12
  have c3 : flJobsCost (setROut σ H0 H1 T0 T1) sJobs ≤ 15 * (126 * cap + 21) := by
    have := lsum_le (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs)))
      (fun j => 18 * (setROut σ H0 H1 T0 T1).val j.v + 3 + 1 + flCost ((setROut σ H0 H1 T0 T1).val j.v) j.bs.length + 1)
      (126 * cap + 21) (fun j hj => by
        have hvj := sJobs_v σ H0 H1 T0 T1 cap hv hH0 hH1 hT0 hT1 j hj
        have hb := (sJobs_facts j hj).2.2
        generalize (setROut σ H0 H1 T0 T1).val j.v = v at hvj ⊢
        generalize j.bs.length = l at hb ⊢
        have m1 : v * (8 * l + 4) ≤ v * 68 := Nat.mul_le_mul_left _ (by omega)
        have m2 : v * l ≤ v * 8 := Nat.mul_le_mul_left _ hb
        unfold flCost
        omega)
    have hl : (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))).length = 15 := rfl
    rw [hl] at this
    exact this
  have c4 : (sClr.map fun r => 3 * (setROut σ H0 H1 T0 T1).val r + 2).sum ≤ 22 * (3 * cap + 2) := by
    have := lsum_le (sClr : List (Fin (bnr nn nrs))) (fun r => 3 * (setROut σ H0 H1 T0 T1).val r + 2) (3 * cap + 2)
      (fun r hr => by have := sClr_v σ H0 H1 T0 T1 cap hv hH0 hH1 hT0 hT1 r hr; omega)
    have hl : (sClr : List (Fin (bnr nn nrs))).length = 22 := rfl
    rw [hl] at this
    exact this
  unfold setRCost
  omega

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
