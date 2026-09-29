import Proof.Supplier.EquationRowRequest
import Proof.Supplier.SupplierCapacity

/-! Exact doubled-equation gate capacity, including the odd padded dimension.
The hundredth-power hypothesis is the natural-number form of the paper's
gate bound g ≤ 2^(s/100); all ceiling and constant slack is paid explicitly. -/
namespace NearCubicWires.RepairOrdinary.EquationRow
open SupplierCapacity SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem doubled_gate_power {s d g : ℕ} (hs : 67 ≤ s) (hd : s≤2*d)
    (hg : g^100≤2^s) : (2*g)^20≤2^d := by
  have hexp : 100+s≤d*5 := by omega
  have hp : ((2*g)^20)^5≤(2^d)^5 := by
    calc
      ((2*g)^20)^5 = 2^100*g^100 := by rw [←pow_mul,mul_pow]
      _ ≤ 2^100*2^s := Nat.mul_le_mul_left _ hg
      _ = 2^(100+s) := (pow_add 2 100 s).symm
      _ ≤ 2^(d*5) := Nat.pow_le_pow_right (by omega) hexp
      _ = (2^d)^5 := pow_mul 2 d 5
  by_contra h
  have hlt : 2^d<(2*g)^20 := by omega
  have hpow : (2^d)^5<((2*g)^20)^5 := by gcongr
  omega

theorem doubled_gateSquare {s g : ℕ} (hs : 67 ≤ s) (hg : g^100≤2^s) :
    (2*g)*(2*g)≤rectangularInnerDimension (2^((s+1)/2)) := by
  exact gateSquare_le_rectangularInnerDimension_of_pow_le
    (doubled_gate_power hs (by omega) hg)

end NearCubicWires.RepairOrdinary.EquationRow
