import Proof.Wire_3_5.Primitive.Writers.HashCosts
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB

/-! # (HASH (d4)), part 5: the HASH writer at one call of the family, within its budget

The HASH writer's constants are functions of the base constants `HB` (the producers' exponents and coefficients: the
call word's `C_w(n+1)^{D_w}`, `needW` and `ThrNumsPoly` bounds, the data stage `D₀`, `C₀`, the FILTER setup's
need and bound, `FiltPipeLe2`'s `K_f`, `D_f`, the THR cap `C_c(n+1)^Z`, `c_r`):

* the dimension `m = k + L + K_H·L³` (`K_L = 0`, `K_H = khOf …`); `Q = 2^m + 1`, `U = Q^{d_N}` (every polynomial
  size of the call is at most `K_atom·U`);
* the register capacity `cap = K_cap·U^{D_n+1}` (above FILTER setup's need), the scrub `R = K_r·U^{d_r}`
  (`D = d_N·d_r`, `C = K_r`: above the unit's cost), the unit budget `R − 1`; the loop `b = 5Q ≥ nHash·5`;
* the data width `V = C_2(n+1)^{D_2}` (the need, `ThrDataOK2`, the numbers' unary word).

**`hash_fam_run`**: at every THR call of the family, the HASH writer `hashM` prints the HASH tape within the budget
`costH …` (`ShellT.hash_ready` at these constants). The class link of the budget is `hash_fam_cost`.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows, P3:2220-2226). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline

/-- **The HASH writer's base constants.** -/
structure HB where
  Cw : ℕ
  Dw : ℕ
  Cnw : ℕ
  Dnw : ℕ
  Kt : ℕ
  Dt : ℕ
  C0 : ℕ
  D0 : ℕ
  Kf : ℕ
  Df : ℕ
  Cn : ℕ
  Dn : ℕ
  Cb : ℕ
  Db : ℕ
  Z : ℕ
  Cc : ℕ
  cr : ℕ

namespace HB
variable (h : HB)

def alpha : ℕ := Nat.clog 2 h.Kt + h.Dt
def cA : ℕ := Nat.clog 2 (12288 * h.Cc + 1)
/-- The dimension's cubic coefficient. -/
def KH : ℕ := HashSizes.khOf h.alpha h.cA h.Z h.Df
/-- The degree (in `Q`) of the call's polynomial sizes. -/
def dN : ℕ := 27 + h.Z + h.Dt + h.Dw
def Katom : ℕ := h.Cw + h.cr + h.Kt + 12288 * h.Cc + 64
def dcap : ℕ := h.Dn + 1
def Kcap : ℕ := 100 * h.Katom + 20000 + h.Cn * (9 * h.Katom) ^ h.Dn
def dr : ℕ := h.dcap * (h.Db + 2) + h.Df + 1
def Kr : ℕ := 1000000 * (h.Kcap * h.Kcap) + h.Cb * (2 * h.Kcap) ^ h.Db + h.Kf * (10 * h.Katom) ^ h.Df +
  1000 * h.Katom + 1000000
/-- The scrub's exponent. -/
def D : ℕ := h.dN * h.dr
def D2 : ℕ := h.Dnw + h.Dt + h.D0 + 1
def C2 : ℕ := h.Cnw + 16 * h.Kt + 32 + h.C0
def Cv : ℕ := h.cr + 19 + 8 * h.KH
/-- The shell budget's exponent. -/
def E : ℕ := ShellT.EcT h.D h.D2 3 1
def d1 : ℕ := h.Dw + h.D2 * h.D0 + 1
def K1 : ℕ := h.Cw + 2 + h.C0 * (3 * h.C2 + 1) ^ h.D0
/-- **The budget's exponent in `Q = 2^m + 1`** (fixed with the floors: no `K_H`, `K_t`, `C₀`, `C_c` in it). -/
def Etot : ℕ := h.d1 * h.E + h.E + h.D + 1
def Ktot : ℕ := ShellT.KcH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH * h.K1 ^ h.E +
  ShellT.KcH h.D h.Kr h.D2 h.C2 3 h.Cv h.cr 1 5 0 h.KH + 5 * (4 * h.Kr + 10)
/-- **The HASH writer's class coefficient** `c_W`. -/
def cW : ℕ := h.Ktot * 2 ^ ((h.Etot * (1 + 0 + h.KH)) ^ 2 + h.Etot)
/-- **The HASH writer's floor envelope**: `c_ψ = E_tot`, every other exponent `0`. -/
def EW : Cost.Envelope := ⟨0, 0, 0, 0, 0, 0, 0, h.Etot⟩

end HB

/-! ## Arithmetic -/

theorem pow_le_pow_of {x y d d' : ℕ} (hxy : x ≤ y) (hy : 1 ≤ y) (hd : d ≤ d') : x ^ d ≤ y ^ d' :=
  le_trans (Nat.pow_le_pow_left hxy d) (Nat.pow_le_pow_right hy hd)

theorem value_eq (D C x : ℕ) : UnaryCalc.value D C x = C * (x + 1) ^ D := rfl

theorem sq2_le (c : ℕ) (hc : 1 ≤ c) : (c + 2) * (c + 2) ≤ 9 * (c * c) := by nlinarith

theorem HB.dr_ge (h : HB) : 1 ≤ h.dr ∧ 2 * h.dcap ≤ h.dr ∧ h.dcap * h.Db ≤ h.dr ∧ h.Df + 1 ≤ h.dr := by
  unfold HB.dr
  have e : h.dcap * (h.Db + 2) = h.dcap * h.Db + 2 * h.dcap := by ring
  omega

/-! ## One call -/

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The call family's facts every HASH bound starts from. -/
theorem fam_n8 {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) : 8 ≤ n := by
  have h1 : 2 ≤ ((gate0 l F).budget kclk coef A a ha).rOf n := hs.2.1
  have h2 : 4 * ((gate0 l F).budget kclk coef A a ha).rOf n ≤ n := hs.2.2.1
  omega

/-- `2·(s·(r/2)) = k`: the star width. -/
theorem fam_two_kh {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    2 * (((callInputs l F kclk coef A a ha).starParams n hs).s * (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)) =
      ((gate0 l F).budget kclk coef A a ha).kOf n := by
  obtain ⟨j, hj⟩ := hs.1
  show 2 * (Nat.log 2 (n / ((gate0 l F).budget kclk coef A a ha).rOf n + 1) *
      (((gate0 l F).budget kclk coef A a ha).rOf n / 2)) =
    ((gate0 l F).budget kclk coef A a ha).rOf n * Nat.log 2 (n / ((gate0 l F).budget kclk coef A a ha).rOf n + 1)
  rw [hj]
  have : (j + j) / 2 = j := by omega
  rw [this]
  ring

/-- The HASH dimension: `m = k + L + 0·L² + K_H·L³`. -/
theorem fam_mOfH {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) (KH : ℕ) :
    NumsXH.mOfH 0 KH ((callInputs l F kclk coef A a ha).starParams n hs) =
      ((gate0 l F).budget kclk coef A a ha).kOf n + Nat.clog 2 (n + 2) + 0 * Nat.clog 2 (n + 2) ^ 2 +
        KH * Nat.clog 2 (n + 2) ^ 3 := by
  unfold NumsXH.mOfH PrimThrW.Shell2.mOfT NumsX.mOf
  rw [fam_two_kh l F kclk coef A a ha hs]
  rfl

/-- The THR cap: `B_T(n) ≤ capK c_r·2^Z·(n+1)^Z`. -/
theorem fam_capT (n : ℕ) :
    ((callInputs l F kclk coef A a ha).filterParams .thr n).cap ≤
      CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l := by
  have h := CallIndexR.cap_leR l F.cr .thr n
  have h2 : (n + 2) ^ CallIndexR.capZR l ≤ 2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc ((callInputs l F kclk coef A a ha).filterParams .thr n).cap
      ≤ CallIndexR.capK F.cr * (n + 2) ^ CallIndexR.capZR l := h
    _ ≤ CallIndexR.capK F.cr * (2 ^ CallIndexR.capZR l * (n + 1) ^ CallIndexR.capZR l) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

end Call

/-! ## The run at one call, within `costH` -/

section Run
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.HashCall NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.Records

end Run

/-! ## The budget's class link -/

section Cost
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem Etot_pos (h : HB) : 1 ≤ h.Etot := by unfold HB.Etot; omega

end Cost

end NearCubicWires.WireExponent3_5.PrimAsm.HashFam
