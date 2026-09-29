import Proof.Wire_3_5.FinalPass.DigsDig5

/-! # `DigsW`'s body, part 9: uniform step bounds for one circuit

The circuit loops need one step bound for every circuit. With every size at most `U` (payload length, `|supp|`,
`|children|`, the selection register, `p`, `d`, `oOff`, the occurrence count), `cDCost … ≤ cDB U` and
`cBCost … ≤ cBB U`, polynomials in `U` (`natBitLength v ≤ v + 1`, `g mod m ≤ g`, `g / m ≤ g`, then monotonicity).
Main declarations: `nbl_le_succ`, `wCost_le`, **`cDCost_le`**, **`cBCost_le`**. Paper quantity: none (the running
time of the program computing the digit populations, polynomial in the input size). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs

theorem nbl_le_succ (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with h | h
  · subst h; simp
  · have := Nat.log_lt_self 2 (Nat.pos_iff_ne_zero.mp h); omega

theorem natCost_le (v U : ℕ) (h : v ≤ U) :
    natCost v ≤ 13 * (U + 1) + 28 + (U + 1) * (50 * (2 * U + 2) + 24) + 7 * U + 3 * (2 * U + 2) := by
  unfold natCost
  have hL : natBitLength v ≤ U + 1 := le_trans (nbl_le_succ v) (by omega)
  gcongr

theorem bitOfCost_le (a d a' d' : ℕ) (ha : a ≤ a') (hd : d ≤ d') : bitOfCost a d ≤ bitOfCost a' d' := by
  unfold bitOfCost halfCost; gcongr

theorem mulStep_le (p p' : ℕ) (h : p ≤ p') : ThrArith.mulStep p ≤ ThrArith.mulStep p' := by unfold ThrArith.mulStep; gcongr

theorem bitCost2_le (p p' : ℕ) (h : p ≤ p') : bitCost2 p ≤ bitCost2 p' := by unfold bitCost2 bitCost; gcongr

theorem modCost2_le (L p L' p' : ℕ) (hL : L ≤ L') (hp : p ≤ p') : modCost2 L p ≤ modCost2 L' p' := by
  unfold modCost2 coreCost
  have := bitCost2_le p p' hp
  gcongr

theorem wCost_le (L p d off o U : ℕ) (hL : L ≤ U) (hp : p ≤ U) (hd : d ≤ U) (hoff : off ≤ U) (ho : o ≤ U) :
    wCost L p d off o ≤ wCost U U U U U := by
  unfold wCost encCost
  have h1 := modCost2_le L p U U hL hp
  have h2 := mulStep_le p U hp
  have h3 := bitOfCost_le p d U U hp hd
  gcongr

theorem bUpdCost_le (p U : ℕ) (hp : p ≤ U) : bUpdCost p ≤ bUpdCost U := by
  unfold bUpdCost
  have := mulStep_le p U hp
  gcongr

/-- The navigation's uniform bound. -/
def navB (U : ℕ) : ℕ :=
  1 + 1 + ((13 * (U + 1) + 28 + (U + 1) * (50 * (2 * U + 2) + 24) + 7 * U + 3 * (2 * U + 2)) + 1 + (7 * U + 1 + 1 +
    ((13 * (U + 1) + 28 + (U + 1) * (50 * (2 * U + 2) + 24) + 7 * U + 3 * (2 * U + 2)) + 1 + (7 * U + 1 + 1 +
    ((18 * U + 3 + 1 + (U * (7 * U + 17) + 1 + 1 + (3 * U + 1))) + 1 + (7 * U + 1 + 1 + (3 * U + 1))))))) +
  1 + (U * (25 * U + 13) + 1 + 1 + (U * (24 * U + 23) + 1))

theorem navCost_le (S m g n Lm U : ℕ) (hS : S ≤ U) (hm : m ≤ U) (hg : g ≤ U) (hn : n ≤ U) (hL : Lm ≤ U) :
    navCost S m g n Lm ≤ navB U := by
  unfold navCost headCost navB
  have h1 := natCost_le S U hS
  have h2 := natCost_le m U hm
  have h3 : g / m ≤ U := le_trans (Nat.div_le_self g m) hg
  have h4 : g % m ≤ U := le_trans (Nat.mod_le g m) hg
  gcongr

/-- One digit-mode circuit's uniform bound. -/
def cDB (U : ℕ) : ℕ :=
  navB U + 1 + (18 * U + 3 + 1 + ((U * (wCost U U U U U + 4) + 1) + 1 + ((7 * U + 3) + 1 + (bUpdCost U + 1 +
    (3 * U + 1)))))

theorem cDCost_le (S m g nz Lm p d off o J U : ℕ) (hS : S ≤ U) (hm : m ≤ U) (hg : g ≤ U) (hn : nz ≤ U)
    (hL : Lm ≤ U) (hp : p ≤ U) (hd : d ≤ U) (hoff : off ≤ U) (ho : o + S ≤ U) (hJ : J ≤ U) :
    cDCost S m g nz Lm p d off o J ≤ cDB U := by
  unfold cDCost cDB
  have h1 := navCost_le S m g nz Lm U hS hm hg hn hL
  have h2 := wCost_le Lm p d off (o + S) U hL hp hd hoff ho
  have h3 := bUpdCost_le p U hp
  gcongr

/-- One base-mode circuit's uniform bound. -/
def cBB (U : ℕ) : ℕ :=
  navB U + 1 + (18 * U + 3 + 1 + (3 + 1 + ((U + 1) * (modCost2 U U + 1 + (U * (7 * U + 12) + 1) + 4) + 1 + 1 +
    ((7 * U + 3) + 1 + (3 * U + 1)))))

theorem cBCost_le (S m g nz Lm p J U : ℕ) (hS : S ≤ U) (hm : m ≤ U) (hg : g ≤ U) (hn : nz ≤ U) (hL : Lm ≤ U)
    (hp : p ≤ U) (hJ : J ≤ U) : cBCost S m g nz Lm p J ≤ cBB U := by
  unfold cBCost cBB
  have h1 := navCost_le S m g nz Lm U hS hm hg hn hL
  have h2 := modCost2_le Lm p U U hL hp
  gcongr

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
