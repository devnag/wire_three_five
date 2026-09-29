import Proof.Wire_3_5.Primitive.SeedFix.C4BudA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymND4

/-! # C4.K item (h), part 2: the SYM stage's steps split into the table-rate part and the rest (generic in the family)

P3:3034-3039 (the decision loop over `8ℓ` bits, each child within the pad `2^ρ`), P3:3011-3016 (the setup), P3:3098-3100:
the wrapper's steps (`wrapCost` of `setupCost3`, the loop at pad `2^ρ`, the finisher), plus the branch's pad and `20`,
are at most the front, the numbers, the moduli, `40(d₂ + ρ) + 80ℓ`, the finisher and the branch (the part of rate below
the table's), plus `(32ℓ + 34)(2^{d₂} + 2^ρ)` (the table-rate part: the printer's table `2^{d₂}`, `d₂ ≤ n − k + 1`, and
the pad) plus the compiler writer's `B₃`.

* **`wrap_split`**.

Paper quantity of the main type: the SYM stage's steps. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost loopZCost loopCost)

/-- **The SYM stage's steps, split.** -/
theorem wrap_split (L : Lay) (w : List Bool) (n CL Cd Cc cD : ℕ) (u : List Bool) (c ell d2 ρ B3 : ℕ)
    (Fm : C4Loop.ChildFam) (samp P : ℕ) (hcell : Fm.cellCost + 1 ≤ 2 ^ ρ) (hb : Fm.bound ≤ 8 * ell) :
    wrapCost (C4Cap.setupCost3 L w n CL Cd Cc cD u c ell d2 ρ B3) Fm (2 ^ ρ) samp + 1 + P + 20 ≤
      (C4Cap.frontCost3 L w n CL Cd Cc + Lay.midCost cD u (2 ^ C4Cap.capExp2 Cc n) c +
        2 * PrimAsm.Modulus.modCost ell + 40 * (d2 + ρ) + 80 * ell + samp + P + 300) +
      (32 * ell + 34) * (2 ^ d2 + 2 ^ ρ) + B3 := by
  unfold wrapCost C4Cap.setupCost3 Lay.tailCost Lay.modsCost srcCost loopZCost loopCost
  have h1 : Fm.bound * (2 * Fm.cellCost + 2 + 1 + (2 * 2 ^ ρ + 4) + 3) ≤ 8 * ell * (4 * 2 ^ ρ + 10) :=
    Nat.mul_le_mul hb (by omega)
  have h2 : 8 * ell * (4 * 2 ^ ρ + 10) = 32 * ell * 2 ^ ρ + 80 * ell := by ring
  have h3 : (32 * ell + 34) * (2 ^ d2 + 2 ^ ρ) = 32 * ell * 2 ^ d2 + 34 * 2 ^ d2 + 32 * ell * 2 ^ ρ + 34 * 2 ^ ρ := by
    ring
  have h4 : 0 ≤ 32 * ell * 2 ^ d2 := Nat.zero_le _
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Bud
