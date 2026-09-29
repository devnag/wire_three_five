import Proof.Wire_3_5.FinalPass.SdC1

/-! # S4 (the seeds phase), part 46: one point's steps, polynomial (P3:3170-3178)

Every cost function one point uses is polynomial in a bound `X` on its arguments: the counters (`incCost`,
`cntCost`), the pair's decoding (`Sample.blkCost`, `Sample.decCost`), one carrier's mask (`Corner.coreCost`,
`gateCost`, `cwCost`, `Pop.passCost`, `Filt.cost7`, `mkCost`, `mkC`), the point (`ptCost`, `sCost`), the center
(`PrimT.Ctr.scanCost`, `p1Cost`, `p2Cost`, `blkCost`, `halfCost`, `ctrCost`). **`ptB_le`**: one point's steps
`ptB ≤ 23000·X⁴` when `X` bounds the star parameters, the counter width, the evaluator's steps, the values, the
carriers' widths, mask lengths, tables and threshold.

Paper quantity of the main type: the per-point cost `pt` of the seeds phase's shape (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR)
open NearCubicWires.SupplierWalk (majorityThreshold)
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner

section Poly
variable {X : ℕ}

theorem xx (hX : 1 ≤ X) : X ≤ X * X := Nat.le_mul_of_pos_left X hX
theorem xxx (hX : 1 ≤ X) : X * X ≤ X * X * X := by
  have := Nat.mul_le_mul_left (X * X) hX
  calc X * X = X * X * 1 := by ring
    _ ≤ X * X * X := this
theorem xxxx (hX : 1 ≤ X) : X * X * X ≤ X * X * X * X := by
  have := Nat.mul_le_mul_left (X * X * X) hX
  calc X * X * X = X * X * X * 1 := by ring
    _ ≤ X * X * X * X := this

theorem incCost_le (T : ℕ) (hT : T ≤ X) (hX : 1 ≤ X) : incCost T ≤ 41 * X := by unfold incCost; omega

theorem cntCost0_le (d T : ℕ) (hd : d ≤ X) (hT : T ≤ X) (hX : 1 ≤ X) : cntCost d T 0 ≤ 81 * X := by
  have := incCost_le T hT hX
  unfold cntCost; omega

theorem sblk_le (s bb : ℕ) (hs : s ≤ X) (hb : bb ≤ X) (h2 : 2 ^ s ≤ X) (hX : 1 ≤ X) :
    Sample.blkCost s bb ≤ 139 * (X * X) := by
  unfold Sample.blkCost
  have m1 : s * (43 * 2 ^ s + 30) ≤ X * (43 * X + 30) := Nat.mul_le_mul hs (by omega)
  have e : X * (43 * X + 30) = 43 * (X * X) + 30 * X := by ring
  have := xx hX
  omega

theorem sdec_le (s bb h tl : ℕ) (hs : s ≤ X) (hb : bb ≤ X) (hh : h ≤ X) (ht : tl ≤ X) (h2 : 2 ^ s ≤ X) (hX : 1 ≤ X) :
    Sample.decCost s bb h tl ≤ 284 * (X * X * X) := by
  unfold Sample.decCost
  have b := sblk_le s bb hs hb h2 hX
  have m1 : h * Sample.blkCost s bb ≤ X * (139 * (X * X)) := Nat.mul_le_mul hh b
  have m2 : h * (30 * bb + 11) ≤ X * (30 * X + 11) := Nat.mul_le_mul hh (by omega)
  have m3 : h * bb ≤ X * X := Nat.mul_le_mul hh hb
  have e1 : X * (139 * (X * X)) = 139 * (X * X * X) := by ring
  have e2 : X * (30 * X + 11) = 30 * (X * X) + 11 * X := by ring
  have := xx hX
  have := xxx hX
  omega

theorem ccore_le (h n : ℕ) (hh : h ≤ X) (hn : n ≤ X) (hX : 1 ≤ X) : Corner.coreCost h n ≤ 460 * (X * X) := by
  unfold Corner.coreCost
  have m1 : n * (110 * h + 110) ≤ X * (110 * X + 110) := Nat.mul_le_mul hn (by omega)
  have e : X * (110 * X + 110) = 110 * (X * X) + 110 * X := by ring
  have := xx hX
  omega

theorem pair_le (h n : ℕ) (hh : h ≤ X) (hn : n ≤ X) (hX : 1 ≤ X) : (n + 1) * (2 * (2 * h + 1)) ≤ 12 * (X * X) := by
  have m : (n + 1) * (2 * (2 * h + 1)) ≤ (X + 1) * (4 * X + 2) := Nat.mul_le_mul (by omega) (by omega)
  have e : (X + 1) * (4 * X + 2) = 4 * (X * X) + 6 * X + 2 := by ring
  have := xx hX
  omega

theorem cgate_le (h n : ℕ) (hh : h ≤ X) (hn : n ≤ X) (hX : 1 ≤ X) : Corner.gateCost h n ≤ 2124 * (X * X) := by
  unfold Corner.gateCost
  have := ccore_le h n hh hn hX
  have := pair_le h n hh hn hX
  have := xx hX
  omega

theorem cw_le (h n m : ℕ) (hh : h ≤ X) (hn : n ≤ X) (hm : m ≤ X) (hX : 1 ≤ X) :
    Corner.cwCost h n m ≤ 2241 * (X * X * X) := by
  unfold Corner.cwCost
  have g := cgate_le h n hh hn hX
  have p := pair_le h n hh hn hX
  have m1 : m * (Corner.gateCost h n + 2) ≤ X * (2124 * (X * X) + 2) := Nat.mul_le_mul hm (by omega)
  have m2 : m * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ X * (1 + 12 * (X * X)) := Nat.mul_le_mul hm (by omega)
  have e1 : X * (2124 * (X * X) + 2) = 2124 * (X * X * X) + 2 * X := by ring
  have e2 : X * (1 + 12 * (X * X)) = X + 12 * (X * X * X) := by ring
  have := xx hX
  have := xxx hX
  omega

theorem mkCost_le (h n g W thr : ℕ) (hh : h ≤ X) (hn : n ≤ X) (hg : g ≤ X) (hW : W ≤ X) (ht : thr ≤ X) (hX : 1 ≤ X) :
    mkCost h n g W thr ≤ 2567 * (X * X * X) := by
  unfold mkCost Pop.passCost Filt.cost7
  have := cw_le h n g hh hn hg hX
  have := xx hX
  have := xxx hX
  omega

theorem mkC_le (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (k : ℕ)
    (hX : 1 ≤ X) (hn : n ≤ X)
    (hk : ∀ hk : k < carriers.length, PrimT.tabH (carriers.get ⟨k, hk⟩) ≤ X ∧
      (maskGates (carriers.get ⟨k, hk⟩)).length ≤ X ∧
      (tableWord (filterTable FP e (maskGates (carriers.get ⟨k, hk⟩)).length)).length ≤ X ∧
      majorityThreshold FP.walkLen ≤ X) :
    mkC FP e carriers k ≤ 2567 * (X * X * X) := by
  unfold mkC
  split_ifs with h
  · obtain ⟨a1, a2, a3, a4⟩ := hk h
    exact mkCost_le _ _ _ _ _ a1 hn a2 a3 a4 hX
  · have := xx hX
    have := xxx hX
    omega

theorem ptCost_le (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (nE V T : ℕ)
    (hX : 1 ≤ X) (hn : n ≤ X) (hnE : nE ≤ X) (hV : V ≤ X) (hT : T ≤ X)
    (hk : ∀ k : ℕ, ∀ hk : k < carriers.length, PrimT.tabH (carriers.get ⟨k, hk⟩) ≤ X ∧
      (maskGates (carriers.get ⟨k, hk⟩)).length ≤ X ∧
      (tableWord (filterTable FP e (maskGates (carriers.get ⟨k, hk⟩)).length)).length ≤ X ∧
      majorityThreshold FP.walkLen ≤ X) :
    ptCost FP e carriers nE V T ≤ 5194 * (X * X * X) := by
  unfold ptCost
  have c0 := mkC_le FP e carriers 0 hX hn (hk 0)
  have c1 := mkC_le FP e carriers 1 hX hn (hk 1)
  have i := incCost_le T hT hX
  have m : V * (incCost T + 4) ≤ X * (45 * X) := Nat.mul_le_mul hV (by omega)
  have e1 : X * (45 * X) = 45 * (X * X) := by ring
  have := xx hX
  have := xxx hX
  omega

theorem sCost_le (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (s bb h tl nE V T : ℕ)
    (hX : 1 ≤ X) (hn : n ≤ X) (hs : s ≤ X) (hb : bb ≤ X) (hh : h ≤ X) (ht : tl ≤ X) (h2 : 2 ^ s ≤ X)
    (hnE : nE ≤ X) (hV : V ≤ X) (hT : T ≤ X)
    (hk : ∀ k : ℕ, ∀ hk : k < carriers.length, PrimT.tabH (carriers.get ⟨k, hk⟩) ≤ X ∧
      (maskGates (carriers.get ⟨k, hk⟩)).length ≤ X ∧
      (tableWord (filterTable FP e (maskGates (carriers.get ⟨k, hk⟩)).length)).length ≤ X ∧
      majorityThreshold FP.walkLen ≤ X) :
    sCost FP e carriers s bb h tl nE V T ≤ 5764 * (X * X * X) := by
  unfold sCost
  have := sdec_le s bb h tl hs hb hh ht h2 hX
  have := ptCost_le FP e carriers nE V T hX hn hnE hV hT hk
  have := xx hX
  have := xxx hX
  omega

theorem scan_le (b : ℕ) (hb : b ≤ X) (hX : 1 ≤ X) : PrimT.Ctr.scanCost b ≤ 2700 * (X * X) := by
  unfold PrimT.Ctr.scanCost
  have m : (b + 2) * (b + 2) ≤ (3 * X) * (3 * X) := Nat.mul_le_mul (by omega) (by omega)
  have e : (3 * X) * (3 * X) = 9 * (X * X) := by ring
  have e2 : 300 * (b + 2) * (b + 2) = 300 * ((b + 2) * (b + 2)) := by ring
  omega

theorem tblk_le (b s : ℕ) (hb : b ≤ X) (hs : s ≤ X) (hX : 1 ≤ X) : PrimT.Ctr.blkCost b s ≤ 8301 * (X * X * X) := by
  unfold PrimT.Ctr.blkCost PrimT.Ctr.p1Cost PrimT.Ctr.p2Cost
  have sc := scan_le b hb hX
  have m1 : (s + 1) * (PrimT.Ctr.scanCost b + 100) ≤ (2 * X) * (2700 * (X * X) + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : (2 * X) * (2700 * (X * X) + 100) = 5400 * (X * X * X) + 200 * X := by ring
  have m2 : (b + 2) * (b + 2) ≤ (3 * X) * (3 * X) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (3 * X) * (3 * X) = 9 * (X * X) := by ring
  have e3 : 300 * (b + 2) * (b + 2) = 300 * ((b + 2) * (b + 2)) := by ring
  have := xx hX
  have := xxx hX
  omega

theorem half_le (P : StarParams) (hr : P.r / 2 ≤ X) (hb : P.b ≤ X) (hs : P.s ≤ X) (hX : 1 ≤ X) :
    PrimT.Ctr.halfCost P ≤ 8328 * (X * X * X * X) := by
  unfold PrimT.Ctr.halfCost
  have bl := tblk_le P.b P.s hb hs hX
  have m : P.r / 2 * (PrimT.Ctr.blkCost P.b P.s + 4) ≤ X * (8301 * (X * X * X) + 4) := Nat.mul_le_mul hr (by omega)
  have e : X * (8301 * (X * X * X) + 4) = 8301 * (X * X * X * X) + 4 * X := by ring
  have := xx hX
  have := xxx hX
  have := xxxx hX
  omega

theorem ctr_le (P : StarParams) (hn : P.n ≤ X) (hr : P.r / 2 ≤ X) (hb : P.b ≤ X) (hs : P.s ≤ X) (hX : 1 ≤ X) :
    PrimT.Ctr.ctrCost P ≤ 16981 * (X * X * X * X) := by
  unfold PrimT.Ctr.ctrCost
  have := half_le P hr hb hs hX
  have := xx hX
  have := xxx hX
  have := xxxx hX
  omega

theorem ptB_le (FP : GapParams) (P : StarParams) (carriers : List (Stars.Carrier P.n)) (s bb h tl nE Vm T : ℕ)
    (e : GapSeed FP) (hX : 1 ≤ X) (hn : P.n ≤ X) (hPb : P.b ≤ X) (hPs : P.s ≤ X) (hPr : P.r / 2 ≤ X)
    (hs : s ≤ X) (hb : bb ≤ X) (hh : h ≤ X) (ht : tl ≤ X) (h2 : 2 ^ s ≤ X) (hsh : s * h ≤ X * X)
    (hnE : nE ≤ X) (hV : Vm ≤ X) (hT : T ≤ X) (hdR : dR P ≤ X) (hdRow : dRow P ≤ X)
    (hk : ∀ k : ℕ, ∀ hk : k < carriers.length, PrimT.tabH (carriers.get ⟨k, hk⟩) ≤ X ∧
      (maskGates (carriers.get ⟨k, hk⟩)).length ≤ X ∧
      (tableWord (filterTable FP e (maskGates (carriers.get ⟨k, hk⟩)).length)).length ≤ X ∧
      majorityThreshold FP.walkLen ≤ X) :
    ptB FP P carriers s bb h tl nE Vm T e ≤ 23000 * (X * X * X * X) := by
  unfold ptB
  have a1 := sCost_le FP e carriers s bb h tl nE Vm T hX hn hs hb hh ht h2 hnE hV hT hk
  have a2 := ctr_le P hn hPr hPb hPs hX
  have a3 := cntCost0_le (dR P) T hdR hT hX
  have a4 := cntCost0_le (dRow P) T hdRow hT hX
  have := xx hX
  have := xxx hX
  have := xxxx hX
  omega

end Poly

end NearCubicWires.WireExponent3_5.FinalPass.Sd
