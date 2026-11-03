import Lean
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Primitive.SeedFix.TS4OBase


noncomputable section
set_option maxRecDepth 4096


/-! # T (#120, thrStage4U), part 13: the capacity need is polynomial

P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`"): `needT l c_r n ≤ NCoef l c_r·(n+1)^{NDeg l}`, the degree
`NDeg l` fixed by the literals (the cap's exponents, W6's `Eth`, the sparse bound's `spA`), the coefficient by `c_r`:

* `two_pow_le` (`(n+2)^d ≤ 2^d (n+1)^d`), `spT_le`, `capNT_le`, `needW_le`;
* `NDeg`, `NCoef`, **`needT_le`**.

Paper quantities of the main type: the v4 stage's capacity need (the THR cap, the sparse count, W6's need). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

variable (l : Literals)

theorem spT_le (n : ℕ) : spT l n ≤ 2 ^ spB l * 4 ^ spA l * (n + 1) ^ spA l := by
  unfold spT
  have h2 := UnionMachine.EwKit.pow_clog_le2 (n + 2) (by omega)
  have h3 : (2 ^ Nat.clog 2 (n + 2)) ^ spA l ≤ (4 * (n + 1)) ^ spA l := Nat.pow_le_pow_left (by omega) _
  calc 2 ^ (spA l * Nat.clog 2 (n + 2) + spB l) = 2 ^ spB l * (2 ^ Nat.clog 2 (n + 2)) ^ spA l := by
        rw [pow_add, ← pow_mul, mul_comm (spA l)]; ring
    _ ≤ 2 ^ spB l * (4 * (n + 1)) ^ spA l := Nat.mul_le_mul_left _ h3
    _ = 2 ^ spB l * 4 ^ spA l * (n + 1) ^ spA l := by rw [mul_pow]; ring

theorem capNT_le (cr n : ℕ) : capNT l cr n ≤
    (2 ^ 40 * PrimAsm.CallIndexR.capK cr * 2 ^ ZmL l + CapNum.cMain (gateCap l) .thr) * (n + 1) ^ ZmL l := by
  unfold capNT
  have h := two_pow_le n (ZmL l)
  have h1 : 1 ≤ (n + 1) ^ ZmL l := Nat.one_le_pow _ _ (by omega)
  have e : (2 ^ 40 * PrimAsm.CallIndexR.capK cr * 2 ^ ZmL l + CapNum.cMain (gateCap l) .thr) * (n + 1) ^ ZmL l =
      2 ^ 40 * (PrimAsm.CallIndexR.capK cr * (2 ^ ZmL l * (n + 1) ^ ZmL l)) +
        CapNum.cMain (gateCap l) .thr * (n + 1) ^ ZmL l := by ring
  rw [e]
  have h2 := Nat.mul_le_mul_left (2 ^ 40) (Nat.mul_le_mul_left (PrimAsm.CallIndexR.capK cr) h)
  have h3 : CapNum.cMain (gateCap l) .thr ≤ CapNum.cMain (gateCap l) .thr * (n + 1) ^ ZmL l :=
    Nat.le_mul_of_pos_right _ h1
  omega

/-- The cap's coefficient at `(n+1)`. -/
noncomputable def capKc (cr : ℕ) : ℕ := PrimAsm.CallIndexR.capK cr * 2 ^ PrimAsm.CallIndexR.capZR l

theorem capZR_pos : 1 ≤ PrimAsm.CallIndexR.capZR l := by unfold PrimAsm.CallIndexR.capZR; omega

theorem capTL_le1 (cr n : ℕ) : capTL l cr n ≤ capKc l cr * (n + 1) ^ PrimAsm.CallIndexR.capZR l := by
  have h := capTL_le l cr n
  have h2 := two_pow_le n (PrimAsm.CallIndexR.capZR l)
  unfold capKc
  calc capTL l cr n ≤ PrimAsm.CallIndexR.capK cr * (n + 2) ^ PrimAsm.CallIndexR.capZR l := h
    _ ≤ PrimAsm.CallIndexR.capK cr * (2 ^ PrimAsm.CallIndexR.capZR l * (n + 1) ^ PrimAsm.CallIndexR.capZR l) :=
      Nat.mul_le_mul_left _ h2
    _ = _ := by ring

theorem needW_le (cr n : ℕ) : W6.needW (W6.litAlg l) 1 (n + capTL l cr n) ≤
    W6.Cth (W6.litAlg l) ^ (48 * 1 + 700) * (capKc l cr + 2) ^ (W6.Eth (W6.litAlg l) * (48 * 1 + 700)) *
      (n + 1) ^ (PrimAsm.CallIndexR.capZR l * (W6.Eth (W6.litAlg l) * (48 * 1 + 700))) := by
  unfold W6.needW
  have hz := capZR_pos l
  have hc := capTL_le1 l cr n
  have hx : n + 1 ≤ (n + 1) ^ PrimAsm.CallIndexR.capZR l := Nat.le_self_pow (by omega) _
  have hm : n + capTL l cr n + 1 ≤ (capKc l cr + 2) * (n + 1) ^ PrimAsm.CallIndexR.capZR l := by
    have e : (capKc l cr + 2) * (n + 1) ^ PrimAsm.CallIndexR.capZR l =
        capKc l cr * (n + 1) ^ PrimAsm.CallIndexR.capZR l + 2 * (n + 1) ^ PrimAsm.CallIndexR.capZR l := by ring
    omega
  have hp := Nat.pow_le_pow_left hm (W6.Eth (W6.litAlg l) * (48 * 1 + 700))
  rw [mul_pow, ← pow_mul] at hp
  calc W6.Cth (W6.litAlg l) ^ (48 * 1 + 700) * (n + capTL l cr n + 1) ^ (W6.Eth (W6.litAlg l) * (48 * 1 + 700))
      ≤ W6.Cth (W6.litAlg l) ^ (48 * 1 + 700) * ((capKc l cr + 2) ^ (W6.Eth (W6.litAlg l) * (48 * 1 + 700)) *
        (n + 1) ^ (PrimAsm.CallIndexR.capZR l * (W6.Eth (W6.litAlg l) * (48 * 1 + 700)))) := Nat.mul_le_mul_left _ hp
    _ = _ := by ring

/-- The need's degree (the literals only). -/
noncomputable def NDeg : ℕ :=
  PrimAsm.CallIndexR.capZR l * (W6.Eth (W6.litAlg l) * (48 * 1 + 700)) + ZmL l + PrimAsm.CallIndexR.capZR l + spA l + 30

/-- The need's coefficient (`c_r` enters). -/
noncomputable def NCoef (cr : ℕ) : ℕ :=
  2 * cr + 116 + 2 ^ spB l * 4 ^ spA l + (2 ^ 40 * PrimAsm.CallIndexR.capK cr * 2 ^ ZmL l + CapNum.cMain (gateCap l) .thr) +
    capKc l cr + 2 + 2 * (W6.Cth (W6.litAlg l) ^ (48 * 1 + 700) * (capKc l cr + 2) ^ (W6.Eth (W6.litAlg l) * (48 * 1 + 700)))

/-- **The v4 stage's need is polynomial**, of degree `NDeg l`. -/
theorem needT_le (cr n : ℕ) : needT l cr n ≤ NCoef l cr * (n + 1) ^ NDeg l := by
  have hx : 1 ≤ n + 1 := by omega
  have up : ∀ d, d ≤ NDeg l → (n + 1) ^ d ≤ (n + 1) ^ NDeg l := fun d hd => Nat.pow_le_pow_right hx hd
  have X1 : 1 ≤ (n + 1) ^ NDeg l := Nat.one_le_pow _ _ hx
  have Xn : n + 1 ≤ (n + 1) ^ NDeg l := by
    have := up 1 (by unfold NDeg; omega); rwa [pow_one] at this
  have t2 := (spT_le l n).trans (Nat.mul_le_mul_left _ (up (spA l) (by unfold NDeg; omega)))
  have t3 := (capNT_le l cr n).trans (Nat.mul_le_mul_left _ (up (ZmL l) (by unfold NDeg; omega)))
  have t4 : PrimAsm.CallIndexR.capK cr * (n + 2) ^ PrimAsm.CallIndexR.capZR l ≤ capKc l cr * (n + 1) ^ NDeg l := by
    have h2 := two_pow_le n (PrimAsm.CallIndexR.capZR l)
    have h3 := up (PrimAsm.CallIndexR.capZR l) (by unfold NDeg; omega)
    unfold capKc
    calc PrimAsm.CallIndexR.capK cr * (n + 2) ^ PrimAsm.CallIndexR.capZR l
        ≤ PrimAsm.CallIndexR.capK cr * (2 ^ PrimAsm.CallIndexR.capZR l * (n + 1) ^ NDeg l) :=
          Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3))
      _ = _ := by ring
  have t5 : (n + 1) ^ 26 ≤ (n + 1) ^ NDeg l := up 26 (by unfold NDeg; omega)
  have t6 := (needW_le l cr n).trans (Nat.mul_le_mul_left _ (up _ (by unfold NDeg; omega)))
  unfold needT NCoef
  generalize (n + 1) ^ NDeg l = X at *
  have e : (2 * cr + 116 + 2 ^ spB l * 4 ^ spA l + (2 ^ 40 * PrimAsm.CallIndexR.capK cr * 2 ^ ZmL l +
      CapNum.cMain (gateCap l) .thr) + capKc l cr + 2 + 2 * (W6.Cth (W6.litAlg l) ^ (48 * 1 + 700) *
        (capKc l cr + 2) ^ (W6.Eth (W6.litAlg l) * (48 * 1 + 700)))) * X =
      2 * cr * X + 116 * X + 2 ^ spB l * 4 ^ spA l * X + (2 ^ 40 * PrimAsm.CallIndexR.capK cr * 2 ^ ZmL l +
        CapNum.cMain (gateCap l) .thr) * X + capKc l cr * X + 2 * X + 2 * (W6.Cth (W6.litAlg l) ^ (48 * 1 + 700) *
          (capKc l cr + 2) ^ (W6.Eth (W6.litAlg l) * (48 * 1 + 700)) * X) := by ring
  rw [e]
  have c1 : 2 * cr ≤ 2 * cr * X := Nat.le_mul_of_pos_right _ X1
  have c2 : 16 * n + 100 ≤ 116 * X := by omega
  omega

end NearCubicWires.WireExponent3_5.PrimT.TS4

end
