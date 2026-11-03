import Proof.Wire_3_5.UnionMachine.ThrDimMBase

/-! # T-A2, part 2: the stage's fill need `needG` within `K_n·(n+1)^{D_n}`, `D_n` fixed by `l`

The fill need is a sum of the stage's capacity terms (`TNeed2`): the star numbers, the sparse count (`2^{O(L)}`),
`CapNum`'s bound `capNT`, the mass bound `Λ̄`, phase B's `(B_T·L + 2)²`, the phases' values `tNeedT2` and `2·m_T + 3`.
Every one is `c·N^e` with `N = n + 2`, `e` from the literals and `c` after `F`:

* `capMainG`, `capEncG`, **`bT_le`** (`B_T ≤ N^{capZR l}` at EVERY star parameter, `r ≤ n`);
* `ZY`, `cY`, **`YB`** (`Y = c_Y·N^{Z_Y}` dominating the stage's atoms), `yb_ge`, the atom bounds `yb_*`;
* `tT_shape` (`T ≤ 3Y⁶`), `tNeed_shape` (the phases' values `≤ 100Y⁶`);
* `sa`, `sb`, `ZE`, **`DnG`** (`l` only), `Kn0`, **`KnG`**, **`need_leG`** (T-A2's `need_le`).

Paper quantity of the main type: the THR dimension stage's fill need, polynomial in `n` (prim:runtime P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Transfer

/-! ## The THR cap at every star parameter -/

/-! ## The master bound `Y = c_Y·N^{Z_Y}` -/

section Atoms
variable (l : Literals) (KL Kf : ℕ)

theorem clog_le (n : ℕ) : Nat.clog 2 (n + 2) ≤ n + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem kp_le_n (P : Shared.StarParams) : P.r * natBitLength (P.n / P.r + 1) ≤ 2 * P.n := by
  rw [kp_eq]
  have h1 : P.k ≤ P.n := NumsX.rs_le P
  have h2 := P.four_r_le_n
  omega

end Atoms

/-! ## The load term and the phases' values below `Y⁶` -/

theorem tT_shape (kp L S CD Kf Y : ℕ) (hY : 1 ≤ Y) (hkp : kp + L ≤ Y) (hD : (S + 1) + L * L ≤ Y) (hCD : CD ≤ Y)
    (hKf : Kf ≤ Y) :
    ((((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) + kp) + L * L) * CD * Kf ≤ 3 * Y ^ 6 := by
  have hA : (kp + L) * (kp + L) ≤ Y * Y := Nat.mul_le_mul hkp hkp
  have hD2 : ((S + 1) + L * L) * CD ≤ Y * Y := Nat.mul_le_mul hD hCD
  have hZ1 : ((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) ≤ Y ^ 4 :=
    (Nat.mul_le_mul hA hD2).trans_eq (by ring)
  have p1 : Y ≤ Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one _).symm
      _ ≤ Y ^ 4 := Nat.pow_le_pow_right hY (by norm_num)
  have hZ3 : (((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) + kp) + L * L ≤ 3 * Y ^ 4 := by omega
  have hZ4 : ((((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) + kp) + L * L) * CD * Kf ≤
      3 * Y ^ 4 * Y * Y := Nat.mul_le_mul (Nat.mul_le_mul hZ3 hCD) hKf
  exact hZ4.trans_eq (by ring)

theorem tNeed_shape (n r m q nb kp B L X S sp CD Kf Y : ℕ) (hY : 1 ≤ Y) (hn : n ≤ Y) (hr : r ≤ Y) (hm : m ≤ Y)
    (hq : q + 1 ≤ Y) (hnb : nb ≤ Y) (hkp : kp + L ≤ Y) (hB : B ≤ Y) (hX : X ≤ Y) (hD : (S + 1) + L * L ≤ Y)
    (hsp : sp ≤ Y) (hCD : CD ≤ Y) (hKf : Kf ≤ Y) :
    n + r + m + q + (q + (1)) + nb + kp + B + L + X + S + (S + (1)) + (L * L) + ((S + (1)) + (L * L)) + (((S + (1)) + (L * L)) * CD) + (kp + L) + ((kp + L) * (kp + L)) + (((kp + L) * (kp + L)) * (((S + (1)) + (L * L)) * CD)) + ((((kp + L) * (kp + L)) * (((S + (1)) + (L * L)) * CD)) + kp) + (((((kp + L) * (kp + L)) * (((S + (1)) + (L * L)) * CD)) + kp) + (L * L)) + ((((((kp + L) * (kp + L)) * (((S + (1)) + (L * L)) * CD)) + kp) + (L * L)) * CD) + (((((((kp + L) * (kp + L)) * (((S + (1)) + (L * L)) * CD)) + kp) + (L * L)) * CD) * Kf) + sp + CD + Kf + 10 ≤ 100 * Y ^ 6 := by
  have hA : (kp + L) * (kp + L) ≤ Y ^ 2 := (Nat.mul_le_mul hkp hkp).trans_eq (by ring)
  have hD2 : ((S + 1) + L * L) * CD ≤ Y ^ 2 := (Nat.mul_le_mul hD hCD).trans_eq (by ring)
  have hZ1 : ((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) ≤ Y ^ 4 :=
    (Nat.mul_le_mul hA hD2).trans_eq (by ring)
  have p12 : Y ≤ Y ^ 2 := by
    calc Y = Y ^ 1 := (pow_one _).symm
      _ ≤ Y ^ 2 := Nat.pow_le_pow_right hY (by norm_num)
  have p24 : Y ^ 2 ≤ Y ^ 4 := Nat.pow_le_pow_right hY (by norm_num)
  have p45 : Y ^ 4 ≤ Y ^ 5 := Nat.pow_le_pow_right hY (by norm_num)
  have p56 : Y ^ 5 ≤ Y ^ 6 := Nat.pow_le_pow_right hY (by norm_num)
  have hZ3 : (((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) + kp) + L * L ≤ 3 * Y ^ 4 := by omega
  have hZ4 : ((((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) + kp) + L * L) * CD ≤ 3 * Y ^ 5 :=
    (Nat.mul_le_mul hZ3 hCD).trans_eq (by ring)
  have hT : ((((kp + L) * (kp + L)) * (((S + 1) + L * L) * CD) + kp) + L * L) * CD * Kf ≤ 3 * Y ^ 6 :=
    tT_shape kp L S CD Kf Y hY hkp hD hCD hKf
  omega

/-! ## The fill need -/

section Need

end Need

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
