import Proof.Wire_3_5.Recovery.RecoveryAssembly

/-! # The recovery leaf `RecoveryLeaf G S₁` (P3:3699-3756, 3831-3852; D1.7)

Realizes the end of the transfer at row B: "Choose the largest `a` such that `m_a ≤ n/2`, and extend the selected core to
`n` inputs by ignoring the suffix. Because `m_{a+1} − m_a = o(m_a)`, the chosen `m_a` is `Θ(n)`" (P3:3740-3742), "the
threshold `e_{t(q)}` [...] with the original per-atom cap" (P3:3731-3733), and the row-B conversion of the per-atom caps
`w_i(q)` into the headline caps (P3:3831-3852), with the recovery obligations of the fused root (`Recovery`: the
language, its `E^NP` certificate, and both hardness statements) at every union leaf of the pinned setup `S₁`.

Paper quantities:
* `recSched`, `recWidth`: the length schedule at the gate constants and the width `q(2^{a(n)})` of the slice `n`;
* **`eventually_slice`**: past an onset, every `SYM∘THR` (`THR∘THR`) circuit on `n` inputs within `⌊w_S(q)⌋`
  (`⌊w_T(q)⌋`) wires agrees with the slice below `1/2 + e_{t(q)}`;
* **`recLanguageCut`**: the recovered language (`false` while `N_{a(n)} = 2^{a(n)}` is below a cutoff);
* **`recLanguageCut_hard`**: `ThrHardAt (1/8) (11/2)` and `SymHardAt (1/8) (9/2)` at every positive multiplier;
* **`recoveryLeaf`**: `Split.RecoveryLeaf G (unionSetupS1 l G)` from `GateRel l G` and the certificate (D1.6), the
  only remaining input, stated for the language this leaf uses. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open Filter

/-- The length schedule at the gate constants. -/
noncomputable def recSched (l : Literals) (G : Split.Gate) (kclk : ℕ) : LengthSchedule :=
  recSchedule (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l)

/-- The width `q(2^{a(n)})` of the slice `n`. -/
noncomputable def recWidth (l : Literals) (G : Split.Gate) (kclk n : ℕ) : ℕ :=
  nativeWidth kclk G.Apad (2 ^ (recSched l G kclk).sourceIdx n)

theorem tendsto_two_pow_sourceIdx (T : LengthSchedule) : Tendsto (fun n => 2 ^ T.sourceIdx n) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => by
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 T.tendsto_sourceIdx b
    exact ⟨N, fun n hn => (hN n hn).trans (Nat.lt_two_pow_self).le⟩

theorem tendsto_recWidth (l : Literals) (G : Split.Gate) (kclk : ℕ) : Tendsto (recWidth l G kclk) atTop atTop :=
  (tendsto_nativeWidth kclk G.Apad).comp (tendsto_two_pow_sourceIdx (recSched l G kclk))

/-- The slice length is at most `(q+1)⁴` once `K₀ ≤ q`. -/
theorem n_succ_le (K₀ q n : ℕ) (hK : K₀ ≤ q) (hn : n ≤ K₀ * q * (Nat.log 2 (Lq q) + 1)) : n + 1 ≤ (q + 1) ^ 4 := by
  have hl : Nat.log 2 (Lq q) + 1 ≤ q + 2 := by
    have h1 := (Nat.log_le_clog 2 (Lq q)).trans (clog_le_self' (Lq q))
    have h2 := Lq_le q
    omega
  have h1 : K₀ * q * (Nat.log 2 (Lq q) + 1) ≤ q * q * (q + 2) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hK) hl
  have h2 : q * q * (q + 2) + 1 ≤ (q + 1) ^ 4 := by nlinarith
  omega

section Leaf

end Leaf

end NearCubicWires.WireExponent3_5.Transfer
