import Proof.Wire_3_5.FinalPass.HashPre1Base

/-! # The HASH printer's occurrence count against `Ψ_aux` (the numbers)

alg:eq-occurrences (P3:1887-1888) at the HASH child request: the charged occurrence count
`max(1,A)·2^m·Q'(P_ex+1)^{Q'd}` is at most `2^{log A + m + Q' + Q'd·log(P_ex+1)}` (**`occP_le_of`**, generic in the
request), and at a HASH call (`log A ≤ k + c_V X²`, `m = 2t + 1`, `Q' = d_Q(L³ + k + L)`, `d = d_D L²`,
`log(P_ex+1) ≤ k + c_{Da} L`) this exponent is at most `C₁·S_aux` with `S_aux = k + L² + (k+L³)L²(k+L)` the auxiliary
load's factor (`Ψ_aux = C_D·S_aux`, P3:3101-3102) (**`occS_num`**).

Paper quantities of the main types: the HASH child request's occurrence count against `Ψ_aux`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine

/-- **The charged occurrence count's exponent** (generic in the request). -/
theorem occP_le_of (a : RepairRepresentation.DecompositionAlgorithm) (R : Req.C3Req) (eV eD : ℕ)
    (hV : R.V.length ≤ 2 ^ eV) (hD : (R.D a).flatten.length + 1 ≤ 2 ^ eD) :
    R.occBoundP a ≤ 2 ^ (eV + R.m + R.P.Q + R.P.Q * R.d * eD) := by
  have hQ : R.P.Q ≤ 2 ^ R.P.Q := (Nat.lt_two_pow_self).le
  have hV1 : max 1 R.V.length ≤ 2 ^ eV := max_le Nat.one_le_two_pow hV
  have hDp : ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d) ≤ 2 ^ (R.P.Q * R.d * eD) := by
    calc _ ≤ (2 ^ eD) ^ (R.P.Q * R.d) := Nat.pow_le_pow_left hD _
      _ = 2 ^ (R.P.Q * R.d * eD) := by rw [← pow_mul, Nat.mul_comm eD]
  unfold Req.C3Req.occBoundP
  rw [pow_add, pow_add, pow_add]
  calc max 1 R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d))
      ≤ 2 ^ eV * 2 ^ R.m * (2 ^ R.P.Q * 2 ^ (R.P.Q * R.d * eD)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hV1) (Nat.mul_le_mul hQ hDp)
    _ = _ := by ring

/-- **The HASH exponent against `S_aux`** (the numbers of `occ_hash`, standalone). -/
theorem occS_num (K L T kh cV cT dQ dD cD S : ℕ) (hL1 : 1 ≤ L) (hkh : 2 * kh = K) (ht : T ≤ cT * (L + 1))
    (hSd : S = K + L ^ 2 + (K + L ^ 3) * L ^ 2 * (K + L)) :
    K + cV * ((L + 1) * (L + 1)) + (2 * T + 1) + dQ * (L * (L * L) + kh + kh + L) +
      dQ * (L * (L * L) + kh + kh + L) * (dD * (L * L)) * (K + cD * L) + 1 ≤
      (4 * cV + 4 * cT + 3 * dQ + 2 * dQ * dD * (cD + 1) + 3) * S := by
  have hL3 : L * (L * L) = L ^ 3 := by ring
  have hLL1 : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hLL : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) _
  have hL3le : L ≤ L ^ 3 := Nat.le_self_pow (by norm_num) _
  have hPS : (K + L ^ 3) * L ^ 2 * (K + L) ≤ S := by rw [hSd]; omega
  have hL3S : L ^ 3 ≤ S := by
    have h1 : L ^ 3 ≤ (K + L ^ 3) * L ^ 2 * (K + L) := by
      calc L ^ 3 = L ^ 3 * 1 * 1 := by ring
        _ ≤ (K + L ^ 3) * L ^ 2 * (K + L) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hLL1) (by omega)
    omega
  have hKS : K ≤ S := by rw [hSd]; omega
  have hL2S : L ^ 2 ≤ S := by rw [hSd]; omega
  have hS1 : 1 ≤ S := by omega
  have p1 : cV * ((L + 1) * (L + 1)) ≤ 4 * cV * S := by
    have h1 : (L + 1) * (L + 1) ≤ 4 * L ^ 2 := by
      have h2 : L + 1 ≤ 2 * L := by omega
      calc (L + 1) * (L + 1) ≤ (2 * L) * (2 * L) := Nat.mul_le_mul h2 h2
        _ = 4 * L ^ 2 := by ring
    calc cV * ((L + 1) * (L + 1)) ≤ cV * (4 * L ^ 2) := Nat.mul_le_mul_left _ h1
      _ ≤ cV * (4 * S) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * cV * S := by ring
  have p2 : 2 * T + 1 ≤ (4 * cT + 1) * S := by
    have h1 : T ≤ cT * (2 * L) := ht.trans (Nat.mul_le_mul_left _ (by omega))
    have h2 : cT * (2 * L) ≤ cT * (2 * S) := Nat.mul_le_mul_left _ (by omega)
    have e : (4 * cT + 1) * S = 2 * (cT * (2 * S)) + S := by ring
    omega
  have p3 : dQ * (L * (L * L) + kh + kh + L) ≤ 3 * dQ * S := by
    have h1 : L * (L * L) + kh + kh + L ≤ 3 * S := by rw [hL3]; omega
    calc dQ * (L * (L * L) + kh + kh + L) ≤ dQ * (3 * S) := Nat.mul_le_mul_left _ h1
      _ = 3 * dQ * S := by ring
  have p4 : dQ * (L * (L * L) + kh + kh + L) * (dD * (L * L)) * (K + cD * L) ≤ 2 * dQ * dD * (cD + 1) * S := by
    have h1 : L * (L * L) + kh + kh + L ≤ 2 * (K + L ^ 3) := by rw [hL3]; omega
    have h2 : K + cD * L ≤ (cD + 1) * (K + L) := by
      have e : (cD + 1) * (K + L) = cD * K + K + cD * L + L := by ring
      omega
    calc dQ * (L * (L * L) + kh + kh + L) * (dD * (L * L)) * (K + cD * L)
        ≤ dQ * (2 * (K + L ^ 3)) * (dD * (L * L)) * ((cD + 1) * (K + L)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) le_rfl) h2
      _ = 2 * dQ * dD * (cD + 1) * ((K + L ^ 3) * L ^ 2 * (K + L)) := by ring
      _ ≤ 2 * dQ * dD * (cD + 1) * S := Nat.mul_le_mul_left _ hPS
  have e : (4 * cV + 4 * cT + 3 * dQ + 2 * dQ * dD * (cD + 1) + 3) * S = 4 * cV * S + (4 * cT + 1) * S + 3 * dQ * S +
      2 * dQ * dD * (cD + 1) * S + 2 * S := by ring
  omega

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
