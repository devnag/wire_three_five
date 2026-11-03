import Proof.SourceAssembly.AdmissionInput

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierCapacity

noncomputable section

theorem foldl_max_le (xs : List ℕ) (z B : ℕ) (hz : z ≤ B) (h : ∀ x ∈ xs, x ≤ B) :
    xs.foldl max z ≤ B := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (max z x) (max_le hz (h x (by simp))) (fun y hy => h y (by simp [hy]))

/-- **The nine summands of `smallSize`.** With `occ+2, alphabet ≤ 2^ell`, the row degree under the printer
inequality `Dg*ell < W`, and the remaining summands under `2^T1`, `2^K`, `2^T5`, `2^T6`, `2^(ell*(ell+9))`,
the whole sum is at most `2^(W + (ell*(ell+9) + T1 + K + T5 + T6) + 4)`. -/
theorem small_sum_le (q inp live occ alph tw walk depth deg ell W Dg T1 T5 T6 K : ℕ)
    (hT1 : q + inp ≤ 2^T1) (hlive : live ≤ K) (hocc : occ + 2 ≤ 2^ell) (halph : alph ≤ 2^ell)
    (hdeg : deg ≤ Dg) (hW : Dg*ell < W) (htw : tw ≤ 2^T5) (hwalk : walk ≤ T6)
    (hdepth : depth ≤ ell + 8) :
    q + inp + 2^live + (occ+2)^(deg+1) + alph^(deg+1) + tw + 2^walk + (occ+2)^(depth+1) + 1 ≤
      2^(W + (ell*(ell+9) + T1 + K + T5 + T6) + 4) := by
  set E := W + (ell*(ell+9) + T1 + K + T5 + T6) with hE
  have hmono : ∀ {x y : ℕ}, x ≤ y → 2^x ≤ 2^y := fun h => Nat.pow_le_pow_right (by decide) h
  have hd : ell*deg ≤ W := by
    have := Nat.mul_le_mul_left ell hdeg
    have : ell*Dg = Dg*ell := Nat.mul_comm _ _
    omega
  have hsq : ell ≤ ell*(ell+9) := Nat.le_mul_of_pos_right _ (by omega)
  have hpow : ∀ {b e : ℕ}, b ≤ 2^ell → e*ell ≤ E → b^e ≤ 2^E := by
    intro b e hb he
    calc b^e ≤ (2^ell)^e := Nat.pow_le_pow_left hb e
      _ = 2^(e*ell) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2^E := hmono he
  have t1 : q + inp ≤ 2^E := hT1.trans (hmono (by omega))
  have t2 : 2^live ≤ 2^E := hmono (by omega)
  have t3 : (occ+2)^(deg+1) ≤ 2^E := hpow hocc (by
    have : (deg+1)*ell = ell*deg + ell := by ring
    omega)
  have t4 : alph^(deg+1) ≤ 2^E := hpow halph (by
    have : (deg+1)*ell = ell*deg + ell := by ring
    omega)
  have t5 : tw ≤ 2^E := htw.trans (hmono (by omega))
  have t6 : 2^walk ≤ 2^E := hmono (by omega)
  have t7 : (occ+2)^(depth+1) ≤ 2^E := hpow hocc (by
    have h1 : (depth+1)*ell ≤ (ell+9)*ell := Nat.mul_le_mul_right ell (by omega)
    have h2 : (ell+9)*ell = ell*(ell+9) := Nat.mul_comm _ _
    omega)
  have t8 : 1 ≤ 2^E := Nat.one_le_two_pow
  have h16 : 2^(E+4) = 16*2^E := by rw [pow_add]; ring
  change _ ≤ 2^(E+4)
  omega

/-- **Eventual smallness.** If `200*W*(K+2) ≤ q`, `m*d ≤ K`, and `2*m*d*(A*L_q^2+4) ≤ q`, then
`d*(W + A*L_q^2 + 4) ≤ q/m`. -/
theorem small_exponent_le (q m d W K A ell : ℕ) (hm : 1 ≤ m) (hload : 200*W*(K+2) ≤ q)
    (hK : m*d ≤ K) (hrest : 2*(m*(d*(A*ell^2+4))) ≤ q) :
    d*(W + A*ell^2 + 4) ≤ q/m := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h1 : 2*((m*d)*W) ≤ 200*W*(K+2) := by
    have : 2*(m*d) ≤ 200*(K+2) := by omega
    nlinarith
  have key : d*(W + A*ell^2 + 4)*m = (m*d)*W + m*(d*(A*ell^2+4)) := by ring
  rw [key]
  omega

/-- The live scale's logarithm passes any bound eventually. -/
theorem logScale_eventually_ge (T : ℕ) : ∀ q, 2^T ≤ q → T ≤ logScale q := by
  intro q hq
  unfold logScale
  by_contra hlt
  rw [not_le] at hlt
  have hle := Nat.le_pow_clog (by decide : 1 < 2) (q+2)
  have hm : 2^Nat.clog 2 (q+2) ≤ 2^(T-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hT : 2^T = 2*2^(T-1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega


end
end NearCubicWires.Admission
