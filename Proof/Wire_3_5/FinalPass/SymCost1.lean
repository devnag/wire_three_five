import Proof.Wire_3_5.FinalPass.SymCap3
import Proof.Wire_3_5.FinalPass.EnumCap7

/-! # The SYM child's cost, part 1: the request's numbers as powers of two (the arithmetic)

P3:1886-1906, 3094-3107 at a SYM call (`k = kOf n`, `L = ⌈log₂(n+2)⌉`, `S = ⌊√B_S⌋`, `U = (k+L)²(S+L)` the load's
SYM term). **`fix_num`**: the compiler input's fixed fields `B = Q' + P_ex + |D| + m + h + p + width + dRow + |cols| + 1`
and the displayed parameters `p + width + P_ex + h + Q' + d + 1` are together below `2^{e_F}`,
`e_F = (c_D + d_Q + d_D + 400)U + (e_H + e_P + 26)L + d_H + d_P + 10` (`efOf`). **`occ_numU`**: the charged occurrence
count `𝒮' = max(1,A)·2^m·Q'(P_ex+1)^{Q'd}` is below `2^{c_O U}`, `c_O = A₁ + 400 + d_Q + c_D·d_Q·d_D` (`coOf`).
Also `dense_length` (`|D| = |flips|·|gates|`) and `two_dRow_le` (`2·dRow ≤ n − k + 1`).

Paper quantities of the main types: the compiler input's description size and `𝒮` at a SYM child request. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch

theorem dense_length (a : RepairRepresentation.DecompositionAlgorithm) {n : ℕ}
    (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ) (flips : List (List Bool)) :
    (Pool.densePool a gates side width flips).length = flips.length * gates.length := by
  unfold Pool.densePool
  rw [List.length_flatMap]
  simp

/-- `2·dRow ≤ n − k + 1` (the printer's rows, `k = rs`). -/
theorem two_dRow_le (P : Shared.StarParams) : 2 * PrimT.C4Geo.dRow P ≤ P.n - P.r * P.s + 1 := by
  show 2 * (P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2) ≤ _
  have h1 := P.r_mul_b_le
  have hR : P.r = 2 * (P.r / 2) := by have := P.r_half_add; omega
  have hsb : P.s ≤ P.b := by
    have := P.b_succ
    have := Nat.lt_two_pow_self (n := P.s)
    omega
  obtain ⟨R, hRd⟩ : ∃ R, R = P.r / 2 := ⟨_, rfl⟩
  rw [← hRd] at hR ⊢
  rw [hR] at h1 ⊢
  have e1 : R * (P.b - P.s) + R * P.s = R * P.b := by rw [← Nat.mul_add]; congr 1; omega
  have e2 : 2 * R * P.s = 2 * (R * P.s) := by ring
  have e3 : 2 * R * P.b = 2 * (R * P.b) := by ring
  rw [e2]
  rw [e3] at h1 ⊢
  omega

/-- The fixed fields' exponent. -/
def efOf (cD dQ dD dH eH dP eP U L : ℕ) : ℕ := (cD + dQ + dD + 400) * U + (eH + eP + 26) * L + dH + dP + 10

/-- The occurrence count's exponent constant. -/
def coOf (A1c dQ cD dD : ℕ) : ℕ := A1c + 400 + dQ + cD * dQ * dD

theorem pow_le_of {x e Z : ℕ} (hx : x ≤ 2 ^ e) (he : e ≤ Z) : x ≤ 2 ^ Z :=
  hx.trans (Nat.pow_le_pow_right (by norm_num) he)

theorem lt_pow_self' (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

theorem kL_le_U (K L S : ℕ) (hL : 1 ≤ L) : K + L ≤ (K + L) * (K + L) * (S + L) := by
  calc K + L = (K + L) * 1 * 1 := by ring
    _ ≤ (K + L) * (K + L) * (S + L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-- `c·(n+1)^e ≤ 2^{c + eL}` when `n + 2 ≤ 2^L`. -/
theorem polyN_le (c e n L : ℕ) (hn : n + 2 ≤ 2 ^ L) : c * (n + 1) ^ e ≤ 2 ^ (c + e * L) := by
  have h1 : (n + 1) ^ e ≤ 2 ^ (e * L) := pow_mono_mul e (by omega)
  calc c * (n + 1) ^ e ≤ 2 ^ c * 2 ^ (e * L) := Nat.mul_le_mul (lt_pow_self' c) h1
    _ = 2 ^ (c + e * L) := by rw [pow_add]

/-- **The fixed fields and the displayed parameters below `2^{e_F}`.** -/
theorem fix_num (K L S n cD dQ dD dH eH dP eP Qv Df Dl m h pr w dR cl dg Pex : ℕ)
    (hL1 : 1 ≤ L) (hn : n + 2 ≤ 2 ^ L) (hcD : 1 ≤ cD)
    (hQ : Qv = dQ * (K + L)) (hDf : Df + 1 ≤ 2 ^ (K + cD * L)) (hDl : Dl ≤ 2 ^ (K + 26 * L + 5))
    (hm : m ≤ 400 * (K + L)) (hh : h = dH * (n + 1) ^ eH) (hpr : pr = dP * (n + 1) ^ eP)
    (hw : w ≤ n + 1) (hdR : dR ≤ n + 1) (hcl : cl ≤ n + 1) (hdg : dg = dD * (S + L)) (hPex : Pex ≤ Df) :
    Qv + Df + Dl + m + h + pr + w + dR + cl + 1 + (pr + w + Pex + h + Qv + dg + 1) ≤
      2 ^ efOf cD dQ dD dH eH dP eP ((K + L) * (K + L) * (S + L)) L := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU]
  have hKU : K + L ≤ U := by rw [hU]; exact kL_le_U K L S hL1
  have hSU : S + L ≤ U := by
    rw [hU]
    calc S + L = 1 * 1 * (S + L) := by ring
      _ ≤ (K + L) * (K + L) * (S + L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (cD + dQ + dD + 400) * U + (eH + eP + 26) * L + dH + dP + 5 := ⟨_, rfl⟩
  have eZ : efOf cD dQ dD dH eH dP eP U L = Z + 5 := by rw [hZ]; unfold efOf; ring
  have eU : (cD + dQ + dD + 400) * U = cD * U + dQ * U + dD * U + 400 * U := by ring
  have eL : (eH + eP + 26) * L = eH * L + eP * L + 26 * L := by ring
  have hZ' : Z = cD * U + dQ * U + dD * U + 400 * U + (eH * L + eP * L + 26 * L) + dH + dP + 5 := by
    rw [hZ, eU, eL]
  -- the terms
  have tQ : Qv ≤ 2 ^ Z := by
    have : Qv ≤ dQ * U := by rw [hQ]; exact Nat.mul_le_mul_left _ hKU
    exact pow_le_of (this.trans (lt_pow_self' _)) (by omega)
  have hcDU : K + cD * L ≤ cD * U := by
    have : K + cD * L ≤ cD * (K + L) := by
      have := Nat.mul_le_mul_right K hcD
      have e : cD * (K + L) = cD * K + cD * L := by ring
      omega
    exact this.trans (Nat.mul_le_mul_left _ hKU)
  have tDf : Df ≤ 2 ^ Z := pow_le_of (show Df ≤ 2 ^ (K + cD * L) by omega) (by omega)
  have tDl : Dl ≤ 2 ^ Z := pow_le_of hDl (by omega)
  have tm : m ≤ 2 ^ Z := by
    have : m ≤ 400 * U := hm.trans (Nat.mul_le_mul_left _ hKU)
    exact pow_le_of (this.trans (lt_pow_self' _)) (by omega)
  have th : h ≤ 2 ^ Z := by
    rw [hh]; exact pow_le_of (polyN_le dH eH n L hn) (by omega)
  have tpr : pr ≤ 2 ^ Z := by
    rw [hpr]; exact pow_le_of (polyN_le dP eP n L hn) (by omega)
  have hnL : n + 1 ≤ 2 ^ L := by omega
  have tw : w ≤ 2 ^ Z := pow_le_of (hw.trans hnL) (by omega)
  have tdR : dR ≤ 2 ^ Z := pow_le_of (hdR.trans hnL) (by omega)
  have tcl : cl ≤ 2 ^ Z := pow_le_of (hcl.trans hnL) (by omega)
  have tdg : dg ≤ 2 ^ Z := by
    have : dg ≤ dD * U := by rw [hdg]; exact Nat.mul_le_mul_left _ hSU
    exact pow_le_of (this.trans (lt_pow_self' _)) (by omega)
  have t1 : 1 ≤ 2 ^ Z := Nat.one_le_two_pow
  rw [eZ, pow_add]
  norm_num
  omega

/-- **The charged occurrence count below `2^{c_O U}`.** -/
theorem occ_numU (K L S A1c cD dQ dD Vl m Qv Df d : ℕ) (hL1 : 1 ≤ L) (hcD : 1 ≤ cD)
    (hV : Vl ≤ 2 ^ (A1c * (K + L))) (hm : m ≤ 400 * (K + L)) (hQ : Qv = dQ * (K + L))
    (hDf : Df + 1 ≤ 2 ^ (K + cD * L)) (hd : d = dD * (S + L)) :
    max 1 Vl * 2 ^ m * (Qv * (Df + 1) ^ (Qv * d)) ≤ 2 ^ (coOf A1c dQ cD dD * ((K + L) * (K + L) * (S + L))) := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU]
  have hKU : K + L ≤ U := by rw [hU]; exact kL_le_U K L S hL1
  have h1 : max 1 Vl ≤ 2 ^ (A1c * (K + L)) := max_le Nat.one_le_two_pow hV
  have h2 : 2 ^ m ≤ 2 ^ (400 * (K + L)) := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : Qv ≤ 2 ^ (dQ * (K + L)) := by rw [hQ]; exact lt_pow_self' _
  have h4 : (Df + 1) ^ (Qv * d) ≤ 2 ^ ((Qv * d) * (K + cD * L)) := pow_mono_mul _ hDf
  have h5 : (Qv * d) * (K + cD * L) ≤ cD * dQ * dD * U := by
    have a1 : K + cD * L ≤ cD * (K + L) := by
      have := Nat.mul_le_mul_right K hcD
      have e : cD * (K + L) = cD * K + cD * L := by ring
      omega
    rw [hQ, hd, hU]
    calc dQ * (K + L) * (dD * (S + L)) * (K + cD * L) ≤ dQ * (K + L) * (dD * (S + L)) * (cD * (K + L)) :=
          Nat.mul_le_mul_left _ a1
      _ = cD * dQ * dD * ((K + L) * (K + L) * (S + L)) := by ring
  have h6 : A1c * (K + L) + 400 * (K + L) + dQ * (K + L) ≤ (A1c + 400 + dQ) * U := by
    have e : A1c * (K + L) + 400 * (K + L) + dQ * (K + L) = (A1c + 400 + dQ) * (K + L) := by ring
    rw [e]; exact Nat.mul_le_mul_left _ hKU
  calc max 1 Vl * 2 ^ m * (Qv * (Df + 1) ^ (Qv * d))
      ≤ 2 ^ (A1c * (K + L)) * 2 ^ (400 * (K + L)) * (2 ^ (dQ * (K + L)) * 2 ^ ((Qv * d) * (K + cD * L))) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
    _ = 2 ^ (A1c * (K + L) + 400 * (K + L) + dQ * (K + L) + (Qv * d) * (K + cD * L)) := by
        rw [pow_add, pow_add, pow_add]; ring
    _ ≤ 2 ^ (coOf A1c dQ cD dD * U) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have e : coOf A1c dQ cD dD * U = (A1c + 400 + dQ) * U + cD * dQ * dD * U := by unfold coOf; ring
        omega

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
