import Proof.Wire_3_5.Primitive.SeedFix.SeedFixSplitT
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixElim
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixCons
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixEmit
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixCoef

/-! # polynomial bounds on the SeedFix stages' step counts, part 1 (the numeric ones)

Each lemma has the shape `f args ≤ C·(q+1)^D` whenever every numeric argument is `≤ q`, with `C`, `D` literals (C1b's
contract for the EAt side conditions' `hK`): the table's inner and multiplication loops, the row passes, the
elimination's record loop (every argument `≤ q`, the prefix not assumed `≤ 2h·ℓ`), Gauss's per-row and full costs,
the deficit, the constraint loop, the split's fields, rotation and target, the cells, the validity loop, the emit and
target copies, and the coefficient writer (`|bs| ≤ q`).

Paper quantity: none (the step counts of `samp:seed`'s machines, P3:3011-3016, 3034-3038, polynomial in their sizes). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SFCost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix

theorem lfsr_eq (ℓ : ℕ) : GF2.lfsrCost ℓ = 8 * ℓ + 13 := by unfold GF2.lfsrCost; omega

theorem innerCost_le (ℓ q : ℕ) (hl : ℓ ≤ q) : innerCost ℓ ≤ 20 * (q + 1) ^ 1 := by
  unfold innerCost; rw [lfsr_eq, pow_one]; omega

theorem mulIterCost_le (ℓ q : ℕ) (hl : ℓ ≤ q) : GF2.mulIterCost ℓ ≤ 24 * (q + 1) ^ 1 := by
  unfold GF2.mulIterCost; rw [lfsr_eq, pow_one]; omega

theorem phACost_le (ℓ q : ℕ) (hl : ℓ ≤ q) : phACost ℓ ≤ 14 * (q + 1) ^ 1 := by
  unfold phACost; rw [pow_one]; omega

theorem phBCost_le (ℓ q : ℕ) (hl : ℓ ≤ q) : phBCost ℓ ≤ 14 * (q + 1) ^ 1 := by
  unfold phBCost; rw [pow_one]; omega

theorem gaussRowCost_le (L q : ℕ) (hl : L ≤ q) : Gauss.rowCost L ≤ 28 * (q + 1) ^ 1 := by
  unfold Gauss.rowCost; rw [pow_one]; omega

theorem gaussCost_le (m v q : ℕ) (hm : m ≤ q) (hv : v ≤ q) : Gauss.gaussCost m v ≤ 100 * (q + 1) ^ 3 :=
  Gauss.gaussCost_le m v (q + 1) (by omega) (by omega) (by omega)

theorem deficitCost_le (v q : ℕ) (hv : v ≤ q) : Deficit.cost v ≤ 3 * (q + 1) ^ 1 := by
  unfold Deficit.cost; rw [pow_one]; omega

theorem fieldCost_le (r q : ℕ) (hr : r ≤ q) : fieldCost r ≤ 8 * (q + 1) ^ 1 := by
  unfold fieldCost; rw [pow_one]; omega

theorem emitInnerCost_le (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) : Emit.emitInnerCost a b ≤ 3 * (q + 1) ^ 1 := by
  unfold Emit.emitInnerCost; rw [pow_one]; omega

theorem tgtInnerCost_le (a b q : ℕ) (ha : a ≤ q) (hb : b ≤ q) : FetchCells.tgtInnerCost a b ≤ 7 * (q + 1) ^ 1 := by
  unfold FetchCells.tgtInnerCost; rw [pow_one]; omega

theorem cellsInnerCost_le (r q : ℕ) (hr : r ≤ q) : Cells.cellsInnerCost r ≤ 97 * (q + 1) ^ 1 := by
  unfold Cells.cellsInnerCost Cells.pairCost Cells.cellCost; rw [pow_one]; omega

theorem consInnerCost_le (m ra rc q : ℕ) (hm : m ≤ q) (ha : ra ≤ q) (hc : rc ≤ q) :
    Cons.consInnerCost m ra rc ≤ 20 * (q + 1) ^ 2 := by
  unfold Cons.consInnerCost Cons.consBodyCost Cons.consTCost
  have h1 : m * (1 + 1 + (1 + 1 + (2 * ra + 1 + 1 + 1) + 1 + (2 * rc + 1 + 1 + 1) + 2) + 2) ≤ q * (4 * q + 16) :=
    Nat.mul_le_mul hm (by omega)
  nlinarith

theorem validInnerCost_le (m r q : ℕ) (hm : m ≤ q) (hr : r ≤ q) : Valid.validInnerCost m r ≤ 30 * (q + 1) ^ 2 := by
  unfold Valid.validInnerCost Valid.validCost
  have h1 : m * ((2 * (2 * r + 1 + 1 + 1) + 2) + 1 + (2 * (2 * r + 1) + 2) + 1 + 1 + 1 + 1 + 2) ≤ q * (8 * q + 19) :=
    Nat.mul_le_mul hm (by omega)
  nlinarith

theorem fieldsTerm_eq (m r : ℕ) : Split.fieldsTermCost m r = 2 * m * (8 * r + 10) + 8 := by
  unfold Split.fieldsTermCost fieldCost; ring

theorem splitFieldsCost_le (ℓ kh q : ℕ) (hl : ℓ ≤ q) (hk : kh ≤ q) :
    Split.splitFieldsCost ℓ kh ≤ 669 * (q + 1) ^ 1 := by
  unfold Split.splitFieldsCost
  rw [fieldsTerm_eq, fieldsTerm_eq, pow_one]
  unfold fieldCost
  omega

theorem rot_eq (kh : ℕ) : Split.rotCost kh = 32 * kh + 110 := by
  unfold Split.rotCost
  simp [List.range_succ]
  ring

theorem splitRotCost_le (kh q : ℕ) (hk : kh ≤ q) : Split.splitRotCost kh ≤ 150 * (q + 1) ^ 1 := by
  unfold Split.splitRotCost; rw [rot_eq, pow_one]; omega

theorem splitTCost_le (ℓ kh TWd q : ℕ) (hl : ℓ ≤ q) (hk : kh ≤ q) (ht : TWd ≤ q) :
    SplitT.splitTCost ℓ kh TWd ≤ 3024 * (q + 1) ^ 1 := by
  unfold SplitT.splitTCost Split.splitFieldsCost Split.splitRotCost
  rw [fieldsTerm_eq, fieldsTerm_eq, rot_eq, pow_one]
  unfold fieldCost
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SFCost
