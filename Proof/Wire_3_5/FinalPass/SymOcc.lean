import Proof.Wire_3_5.FinalPass.SampPre

/-! # The printer's gate budget at a call, from the load condition

"It suffices that `max{Ψ_i, Ψ_aux} ≤ c₀(n−k)` for a sufficiently small positive constant `c₀`" with
`Ψ_S = C_D((k+L)²d_S + k + L²)`, `d_S = C_D(√B + L)` (P3:3094-3107): the call's fit (`Fits.pre`: `c_ψ·ψ ≤ n`) and a
load constant `C_D` above a floor give alg:eq-budget's `log A + m + log Q' + Q'd·log(P_ex+1) ≤ n_out/100`
(P3:1897-1900) with `n_out = dRow ≥ (n−k)/2`. Why the floor: at `C_D·c_ψ` small, calls of length
`n ≈ 2^{4σ}` exist whose `n` is below `C·L⁴(k+L)`, and there the budget fails.
* `loadSym_le` (`C_D²(k+L)²(⌊√B_S⌋+L) ≤ ψ`), `kL_mul_le` (`C_D(k+L) ≤ ψ`), `two_dRow_ge` (`n − k ≤ 2·dRow`);
* **`occ_num`**: the budget from a linear part `C_D·X ≤ C₁ψ`, a quadratic part `C_D²·Y ≤ C₂ψ`, `160C₁ ≤ C_D`,
  `160C₂ ≤ C_D²`, `ψ ≤ n`, `2k ≤ ψ`.
Paper quantities of the main types: the load `ψ`, the printer's rows `dRow`, the budget of alg:eq-budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

/-- `C_D²(k+L)²(⌊√B_S⌋+L) ≤ ψ` (through `Ψ_S`). -/
theorem loadSym_le (CD k L BT BS : ℕ) :
    CD * CD * ((k + L) * (k + L) * (Nat.sqrt BS + L)) ≤ loadPsi CD k L BT BS := by
  have h1 : loadSym CD k L BS ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_trans (le_max_left _ _) (le_max_right _ _)
  refine le_trans ?_ h1
  unfold loadSym sqrtUp
  have e : CD * CD * ((k + L) * (k + L) * (Nat.sqrt BS + L)) = CD * ((k + L) ^ 2 * (CD * (Nat.sqrt BS + L))) := by ring
  rw [e]
  apply Nat.mul_le_mul_left
  have : (k + L) ^ 2 * (CD * (Nat.sqrt BS + L)) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt BS + 1 + L)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

/-- `C_D(k+L) ≤ ψ` (through `Ψ_aux`). -/
theorem kL_mul_le (CD k L BT BS : ℕ) : CD * (k + L) ≤ loadPsi CD k L BT BS := by
  have h1 : loadAux CD k L ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine le_trans ?_ h1
  unfold loadAux
  apply Nat.mul_le_mul_left
  have h2 : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  omega

/-- `n − k ≤ 2·dRow` (the printer's rows: `r/2` blocks of `b − s` bits and `⌈(n−rb)/2⌉` more, `k = rs`). -/
theorem two_dRow_ge (P : Shared.StarParams) : P.n - P.r * P.s ≤ 2 * PrimT.C4Geo.dRow P := by
  show _ ≤ 2 * (P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2)
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

/-- **The printer's budget from the load**: with a linear part `C_D·(X+1) ≤ C₁ψ`, a quadratic part `C_D²·Y ≤ C₂ψ`,
`160C₁ ≤ C_D`, `160C₂ ≤ C_D²`, `1 ≤ C_D`, `ψ ≤ n`, `2k ≤ ψ` and `n − k ≤ 2·dRow`: `10(2(X + Y) + 2) ≤ dRow`. -/
theorem occ_num (ψ n k dRow CD X Y C1 C2 : ℕ) (hCD1 : 1 ≤ CD) (hA : CD * (X + 1) ≤ C1 * ψ) (hB : CD * CD * Y ≤ C2 * ψ)
    (h1 : 160 * C1 ≤ CD) (h2 : 160 * C2 ≤ CD * CD) (hn : ψ ≤ n) (hk : 2 * k ≤ ψ) (hd : n - k ≤ 2 * dRow) :
    10 * (2 * (X + Y) + 2) ≤ dRow := by
  have hCD : 0 < CD := hCD1
  have a1 : CD * (160 * (X + 1)) ≤ CD * ψ := by
    calc CD * (160 * (X + 1)) = 160 * (CD * (X + 1)) := by ring
      _ ≤ 160 * (C1 * ψ) := Nat.mul_le_mul_left _ hA
      _ = (160 * C1) * ψ := by ring
      _ ≤ CD * ψ := Nat.mul_le_mul_right _ h1
  have a2 : 160 * (X + 1) ≤ ψ := Nat.le_of_mul_le_mul_left a1 hCD
  have hCD2 : 0 < CD * CD := Nat.mul_pos hCD hCD
  have b1 : CD * CD * (160 * Y) ≤ CD * CD * ψ := by
    calc CD * CD * (160 * Y) = 160 * (CD * CD * Y) := by ring
      _ ≤ 160 * (C2 * ψ) := Nat.mul_le_mul_left _ hB
      _ = (160 * C2) * ψ := by ring
      _ ≤ CD * CD * ψ := Nat.mul_le_mul_right _ h2
  have b2 : 160 * Y ≤ ψ := Nat.le_of_mul_le_mul_left b1 hCD2
  omega

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

