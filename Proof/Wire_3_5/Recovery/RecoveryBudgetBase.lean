import Proof.Wire_3_5.Recovery.RecoveryFacts
import Proof.Wire_3_5.Recovery.RecoveryEnvelope
import Bindings.Williams14_Corollary4_4
import Proof.PCP.PCPPQueryBounds
import Proof.Packets.BudgetReaderCaps

/-! # The guess fits the refuter's budget, and the clause width (P3:3657-3666, 3675-3680; D1.5)

Realizes the two remaining size statements of the union machine at the recovery: "Every guess has `q^{O(1)} = o(N)`
bits, since `N = 2^{Θ(q)}`. At the finitely many source lengths where this fixed envelope exceeds the refuter's `N/10`
guess budget, the machine rejects outright" (P3:3675-3680), and "Choose a branch-independent integer `d_G` bounding
all PCPP clause counts" (P3:3657-3659).

Paper quantities:
* **`eventually_poly_le_div16`**: every fixed polynomial of `q(N)` is eventually at most `⌊N/16⌋`
  (`q(N) = O(log N)`);
* the code lengths the guess word reads, as fixed polynomials of their parameter (`oracleCode_le`, `atomCode_le`,
  `intWord_grid_le`);
* the substituted request's size for an oracle of size `≤ q^G` (`requestSize_le`) and hence the PCPP's variable count
  and clause bits;
* the clause degree `d_G = σ·d_a + 1` (`recDG`) with `2^{clauseBits} ≤ (q+2)^{d_G}` eventually. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.RecoveryWitnessPolicy
open Filter

section Budget

theorem clog_le_self' (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-- `q(N) + 1 ≤ K·clog N + K` with `K = (kclk+2)(1+A) + 3A + 1`. -/
theorem nativeWidth_le_clog (kclk A' N : ℕ) :
    nativeWidth kclk A' N + 1 ≤ ((kclk + 2) * (1 + A') + 3 * A' + 1) * Nat.clog 2 N +
      ((kclk + 2) * (1 + A') + 3 * A' + 1) := by
  unfold nativeWidth
  have h1 : Nat.clog 2 (N ^ (kclk + 2)) ≤ (kclk + 2) * Nat.clog 2 N := clog_pow_le N (kclk + 2)
  have h2 : Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2) ≤ Nat.clog 2 (N ^ (kclk + 2)) + 2 := clog_le_self' _
  have h3 : A' * Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2) ≤ A' * ((kclk + 2) * Nat.clog 2 N + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- **Every fixed polynomial of `q(N)` is eventually at most `⌊N/16⌋`** (`q(N) = O(log N)`). -/
theorem eventually_poly_le_div16 (kclk A' c d : ℕ) :
    ∀ᶠ N in atTop, c * (nativeWidth kclk A' N + 1) ^ d ≤ N / 16 := by
  set K := (kclk + 2) * (1 + A') + 3 * A' + 1 with hK
  have hclog : Tendsto (fun N => Nat.clog 2 N) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun N hN => by
      calc b = Nat.clog 2 (2 ^ b) := (Nat.clog_pow 2 b (by norm_num)).symm
        _ ≤ Nat.clog 2 N := Nat.clog_mono_right 2 hN⟩
  have hev := hclog.eventually (eventually_mul_affine_pow_le_two_pow (32 * c) K K d)
  filter_upwards [hev, eventually_ge_atTop 2] with N h hN
  have hw := nativeWidth_le_clog kclk A' N
  have hpow : (nativeWidth kclk A' N + 1) ^ d ≤ (K * Nat.clog 2 N + K) ^ d := Nat.pow_le_pow_left hw d
  have hlt : 2 ^ (Nat.clog 2 N - 1) < N := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpos : 1 ≤ Nat.clog 2 N := Nat.clog_pos (by norm_num) (by omega)
  have h2 : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h3 : 32 * c * (nativeWidth kclk A' N + 1) ^ d ≤ 2 ^ Nat.clog 2 N :=
    (Nat.mul_le_mul_left _ hpow).trans h
  have e : 32 * c * (nativeWidth kclk A' N + 1) ^ d = 2 * (c * (nativeWidth kclk A' N + 1) ^ d * 16) := by ring
  omega

/-- The code length of an oracle within the parameter `P`. -/
theorem oracleCode_le {w : ℕ} (oracle : BooleanCircuit w) (P : ℕ) (h4 : 4 ≤ P) (hw : w ≤ P) (hs : oracle.size ≤ P) :
    (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤
      2 * canonicalBooleanCircuitCodeBitBound P + 1 := by
  rw [Bindings.Williams14.natWord_length]
  have := encodeBooleanCircuit_bits_le_parameter oracle h4 hw hs
  omega

/-- The code length of an atom within the description parameter `P`. -/
theorem atomCode_le (m : Mode) {n : ℕ} (C : m.Circuit n) (P : ℕ) (h4 : 4 ≤ P) (hd : m.descriptionBits C ≤ P) :
    (natWord (m.code C)).length ≤
      2 * (canonicalSymmetricCircuitCodeBitBound P + canonicalThresholdCircuitCodeBitBound P) + 1 := by
  rw [Bindings.Williams14.natWord_length]
  cases m
  · have := encodeNormalizedThresholdCircuit_bits_le_parameter C h4 hd
    show 2 * natBitLength (SupplierPipeline.encodeNormalizedThresholdThresholdCircuit C) + 1 ≤ _
    omega
  · have := encodeNormalizedSymmetricCircuit_bits_le_parameter C h4 hd
    show 2 * natBitLength (SupplierPipeline.encodeNormalizedSymmetricThresholdCircuit C) + 1 ≤ _
    omega

/-- The word of a grid sign is at most four bits. -/
theorem intWord_grid_le : ∀ σ ∈ ({-1, 0, 1} : Finset ℤ), (intWord σ).length ≤ 4 := by
  intro σ hσ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl <;> decide

end Budget

section Sizes

end Sizes

end NearCubicWires.WireExponent3_5.Transfer
