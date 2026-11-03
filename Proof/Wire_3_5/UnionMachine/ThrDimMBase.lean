import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase
import Proof.Wire_3_5.Primitive.Writers.NumsXT2Run
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ShellT2
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit
import Proof.Wire_3_5.Primitive.Writers.SymNeedBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4V
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase

/-! # T-A2, part 1: the THR dimension `m_T` against the load `Ψ_T` (P3:3094-3107)

The stage (`ThrDim.mTG`) writes `m_T = mOfT K_L P + T` with `T = K_f·C_D·((k'+L)²·C_D·(⌈√(B_T·L)⌉+1+L²) + k' + L²)`
and `k' = r·natBitLength(n/r+1)`; the load is `Ψ_T = C_D((k+L)²·C_D(⌊√(B_T·L)⌋+1+L²) + k + L²)` (`loadThr`,
`d_T = C_D(√(B_T L) + L²)`, P3:3094-3100). At a star parameter (`4r ≤ n`, so `s = ⌊log₂(n/r+1)⌋ ≥ 1`):

* `kp_eq` (`k' = k + r`), `s_pos`, `r_le_k`, **`k_le_kp`**, **`kp_le_2k`** (`k ≤ k' ≤ 2k`);
* `sqrt_le_ncs`, `ncs_le_sqrt` (`⌊√X⌋ ≤ ⌈√X⌉ ≤ ⌊√X⌋ + 1`);
* `ge_shape`, **`m_geG`** (`mOfT + K_f·Ψ_T ≤ m_T`); `le_shape`, **`m_leG`** (`m_T ≤ mOfT + 8·K_f·Ψ_T`).

Paper quantity of the main types: the THR writer's dimension `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Transfer

/-! ## `k' ∈ [k, 2k]` -/

/-- `k' = r·natBitLength(n/r+1) = k + r`. -/
theorem kp_eq (P : Shared.StarParams) : P.r * natBitLength (P.n / P.r + 1) = P.k + P.r := by
  show P.r * (Nat.log 2 (P.n / P.r + 1) + 1) = P.r * Nat.log 2 (P.n / P.r + 1) + P.r
  ring

/-- `s ≥ 1` (`n/r ≥ 4`). -/
theorem s_pos (P : Shared.StarParams) : 1 ≤ P.s := by
  have hr := P.two_le_r
  have h4 := P.four_r_le_n
  have hdiv : 4 ≤ P.n / P.r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  exact Nat.le_log_of_pow_le (by norm_num) (by rw [pow_one]; omega)

theorem r_le_k (P : Shared.StarParams) : P.r ≤ P.k := by
  have := s_pos P
  show P.r ≤ P.r * P.s
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- **`k ≤ k'`**. -/
theorem k_le_kp (P : Shared.StarParams) : P.k ≤ P.r * natBitLength (P.n / P.r + 1) := by
  rw [kp_eq]; omega

/-- **`k' ≤ 2k`**. -/
theorem kp_le_2k (P : Shared.StarParams) : P.r * natBitLength (P.n / P.r + 1) ≤ 2 * P.k := by
  rw [kp_eq]; have := r_le_k P; omega

/-! ## The square roots -/

theorem sqrt_le_ncs (X : ℕ) : Nat.sqrt X ≤ CanonicalFourfoldRowProgram.natCeilSqrt X := by
  unfold CanonicalFourfoldRowProgram.natCeilSqrt
  dsimp only
  split_ifs <;> omega

theorem ncs_le_sqrt (X : ℕ) : CanonicalFourfoldRowProgram.natCeilSqrt X ≤ Nat.sqrt X + 1 := by
  unfold CanonicalFourfoldRowProgram.natCeilSqrt
  dsimp only
  split_ifs <;> omega

/-! ## The two dimension bounds -/

/-- The lower bound's arithmetic: `K_f·Ψ_T ≤ T` from `k ≤ k'`, `⌊√X⌋ ≤ ⌈√X⌉`. -/
theorem ge_shape (CD Kf k kp L X : ℕ) (hk : k ≤ kp) :
    Kf * (CD * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2)) + k + L ^ 2)) ≤
      ((((kp + L) * (kp + L)) * (((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L) * CD) + kp) + L * L) *
        CD * Kf := by
  have hS := sqrt_le_ncs X
  have hA : (k + L) ^ 2 ≤ (kp + L) * (kp + L) := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have hD : Nat.sqrt X + 1 + L ^ 2 ≤ (CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L := by
    rw [pow_two]; omega
  have h1 : (k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2)) ≤
      ((kp + L) * (kp + L)) * (CD * ((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L)) :=
    Nat.mul_le_mul hA (Nat.mul_le_mul_left _ hD)
  have h2 : L ^ 2 = L * L := pow_two L
  calc Kf * (CD * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2)) + k + L ^ 2))
      ≤ Kf * (CD * (((kp + L) * (kp + L)) * (CD * ((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L)) +
          kp + L * L)) := by
        apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
    _ = _ := by ring

/-- The upper bound's arithmetic: `T ≤ 8·K_f·Ψ_T` from `k' ≤ 2k`, `⌈√X⌉ ≤ ⌊√X⌋ + 1`. -/
theorem le_shape (CD Kf k kp L X : ℕ) (hk2 : kp ≤ 2 * k) :
    ((((kp + L) * (kp + L)) * (((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L) * CD) + kp) + L * L) *
        CD * Kf ≤
      8 * Kf * (CD * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2)) + k + L ^ 2)) := by
  have hS := ncs_le_sqrt X
  have hA : (kp + L) * (kp + L) ≤ 4 * (k + L) ^ 2 := by
    have h : kp + L ≤ 2 * (k + L) := by omega
    calc (kp + L) * (kp + L) ≤ (2 * (k + L)) * (2 * (k + L)) := Nat.mul_le_mul h h
      _ = 4 * (k + L) ^ 2 := by ring
  have hD : (CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L ≤ 2 * (Nat.sqrt X + 1 + L ^ 2) := by
    rw [pow_two]; omega
  have h1 : ((kp + L) * (kp + L)) * (((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L) * CD) ≤
      8 * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2))) :=
    calc ((kp + L) * (kp + L)) * (((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L) * CD)
        ≤ (4 * (k + L) ^ 2) * ((2 * (Nat.sqrt X + 1 + L ^ 2)) * CD) := Nat.mul_le_mul hA (Nat.mul_le_mul_right _ hD)
      _ = 8 * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2))) := by ring
  have h2 : L * L = L ^ 2 := (pow_two L).symm
  calc ((((kp + L) * (kp + L)) * (((CanonicalFourfoldRowProgram.natCeilSqrt X + 1) + L * L) * CD) + kp) + L * L) *
        CD * Kf
      ≤ (8 * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2)) + k + L ^ 2)) * CD * Kf := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
    _ = 8 * Kf * (CD * ((k + L) ^ 2 * (CD * (Nat.sqrt X + 1 + L ^ 2)) + k + L ^ 2)) := by ring

section Gate

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
