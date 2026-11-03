import Proof.Wire_3_5.Outer35.DescriptorLog
import Proof.Wire_3_5.Assembly.GateUnion

/-!
# The description-length guard holds for every `q^G`-gate circuit, eventually

Paper v2, Lemma H.7(a): "For all sufficiently large `a`, with `N = 2^a` and `q = q(N)`, and for all circuits
`Γ_src, Γ_pf` with `q` inputs and at most `q^G` gates: the description of `Γ_src` has fewer than `λ_a` bits", with the
proof "The description has at most `c_fmt(q^G+1)log₂(q^G+q+2) ≤ 2c_fmt(G+1)(C_clk+1)^G a^G log₂(2(C_clk+1)a)` bits,
which is `o(a^{G+1}) = o(λ_a)`"; "Put `G' = G+1`, `λ_a = a^{G'}`" (§H.6); and §H.5: "By Lemma H.7(a), the
description-length guard on `Γ_src` likewise rejects a well-formed source circuit at only finitely many lengths".

* `lenFit_gen`: for any clock exponent `k`, padding constant `A` and size exponent `G ≥ 1`, past some `a₀` every circuit
  on `q = q(2^a)` inputs with `|Γ| + 1 ≤ (q+1)^G` has a description of at most `a^{G+1}` bits
  (`descriptor_length_le_log`, `q(2^a) + 1 ≤ C·(a+1)`, and `K·(log₂ a + 1) ≤ a` eventually);
* **`lenFit35`**: at the gate, every circuit within the size cap `oracleSizeBound (oracleDeg l) q` satisfies the guard
  `SrcFits (lenG l) a` (`λ_a = a^{capExp l + 1}`, `instLength_lenG`).

Paper quantity of the main statement: the guard `|⟨Γ_src⟩| ≤ λ_a` (`Outer.SrcFits`).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Outer35

open _root_.NearCubicWires _root_.NearCubicWires.RepairRepresentation _root_.NearCubicWires.RepairOrdinary
open NearCubicGates.Close

/-- `q(2^a) + 1 ≤ C (a + 1)` for a constant `C` depending on the clock and `A_pad` only. -/
theorem widthOf_lin (k A a : ℕ) : Outer.widthOf k A (2 ^ a) + 1 ≤ ((A + 1) * (k + 2) + 3 * A + 1) * (a + 1) := by
  unfold Outer.widthOf
  rw [Outer.clkLog_two_pow]
  have hc : Nat.clog 2 (a * (k + 2) + 2) ≤ a * (k + 2) + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have h1 : A * Nat.clog 2 (a * (k + 2) + 2) ≤ A * (a * (k + 2) + 2) := Nat.mul_le_mul_left _ hc
  nlinarith

theorem natBitLength_lt (x : ℕ) : x < 2 ^ natBitLength x := by
  unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem natBitLength_le_of_lt_pow (x m : ℕ) (hx : 1 ≤ x) (h : x < 2 ^ m) : natBitLength x ≤ m := by
  unfold natBitLength
  have := Nat.log_lt_of_lt_pow (b := 2) (by omega) h
  omega

theorem natBitLength_mul_le (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    natBitLength (x * y) ≤ natBitLength x + natBitLength y := by
  apply natBitLength_le_of_lt_pow _ _ (Nat.one_le_iff_ne_zero.2 (by positivity))
  rw [pow_add]
  exact Nat.mul_lt_mul'' (natBitLength_lt x) (natBitLength_lt y)

theorem natBitLength_pow_le (y G : ℕ) (hy : 1 ≤ y) (hG : 1 ≤ G) : natBitLength (y ^ G) ≤ G * natBitLength y := by
  apply natBitLength_le_of_lt_pow _ _ (Nat.one_le_pow _ _ hy)
  rw [mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left (natBitLength_lt y) (by omega)

theorem natBitLength_pos (x : ℕ) : 1 ≤ natBitLength x := by unfold natBitLength; omega

/-- Exponentials beat linear functions: `K (m + 1) ≤ 2^m` for `m ≥ 2K + 4`. -/
theorem exp_beats_lin (K : ℕ) : ∀ m, 2 * K + 4 ≤ m → K * (m + 1) ≤ 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have h1 : K + 1 ≤ 2 ^ K := Nat.lt_two_pow_self
    have e : 2 ^ (2 * K + 4) = 16 * (2 ^ K * 2 ^ K) := by rw [← pow_add]; ring_nf
    rw [e]
    nlinarith
  | succ m hm ih =>
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    rw [pow_succ]
    nlinarith

/-- `K (natBitLength a) ≤ a` past `2^{2K+4}`. -/
theorem lin_log_le (K a : ℕ) (ha : 2 ^ (2 * K + 4) ≤ a) : K * natBitLength a ≤ a := by
  have ha0 : a ≠ 0 := by have := Nat.one_le_two_pow (n := 2 * K + 4); omega
  have hm : 2 * K + 4 ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) ha
  have h1 := exp_beats_lin K (Nat.log 2 a) hm
  have h2 := Nat.pow_log_le_self 2 ha0
  unfold natBitLength
  omega

/-- **The guard eventually holds, generically**: past some `a₀`, every circuit on `q(2^a)` inputs with
`|Γ| + 1 ≤ (q+1)^G` has a description of at most `a^{G+1}` bits. -/
theorem lenFit_gen (k A G : ℕ) (hG : 1 ≤ G) :
    ∃ a₀ : ℕ, ∀ a, a₀ ≤ a → ∀ {m : ℕ} (Γ : BooleanCircuit m), m = Outer.widthOf k A (2 ^ a) →
      Γ.size + 1 ≤ (m + 1) ^ G → (PCPPNative.descriptor Γ).length ≤ a ^ (G + 1) := by
  set C1 := (A + 1) * (k + 2) + 3 * A + 1 with hC1
  set c0 := natBitLength (2 * C1) with hc0
  set K := 6 * (2 * C1) ^ G * (G * c0 + 3 + G) with hK
  refine ⟨2 ^ (2 * K + 4) + 1, fun a ha m Γ hm hs => ?_⟩
  have ha1 : 1 ≤ a := by have := Nat.one_le_two_pow (n := 2 * K + 4); omega
  have hlin := widthOf_lin k A a
  rw [← hm] at hlin
  set X := (m + 1) ^ G with hX
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hmX : m + 1 ≤ X := by rw [hX]; exact Nat.le_self_pow (by omega) _
  -- the description
  have hd := descriptor_length_le_log Γ
  have h4 : m + Γ.size + 4 ≤ 4 * X := by omega
  have hn4 : natBitLength (m + Γ.size + 4) ≤ natBitLength X + 2 := by
    refine (natBitLength_mono h4).trans ?_
    apply natBitLength_le_of_lt_pow _ _ (by omega)
    rw [pow_add]
    have := natBitLength_lt X
    omega
  have hnX : natBitLength X ≤ G * natBitLength (m + 1) := natBitLength_pow_le _ _ (by omega) hG
  -- the width
  have hC1pos : 1 ≤ C1 := by omega
  have hw : m + 1 ≤ 2 * C1 * a := by nlinarith
  have hnm : natBitLength (m + 1) ≤ c0 + natBitLength a :=
    (natBitLength_mono hw).trans (natBitLength_mul_le _ _ (by omega) ha1)
  have hXa : X ≤ (2 * C1) ^ G * a ^ G := by
    rw [hX, ← mul_pow]; exact Nat.pow_le_pow_left hw _
  -- the log factor
  have hna := natBitLength_pos a
  have hlog : natBitLength (m + Γ.size + 4) + 1 ≤ (G * c0 + 3 + G) * natBitLength a := by
    have h1 : G * natBitLength (m + 1) ≤ G * c0 + G * natBitLength a := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hnm
    have h2 : G * c0 + 3 ≤ (G * c0 + 3) * natBitLength a := Nat.le_mul_of_pos_right _ hna
    have h3 : (G * c0 + 3 + G) * natBitLength a = (G * c0 + 3) * natBitLength a + G * natBitLength a := by ring
    omega
  have hKa : K * natBitLength a ≤ a := lin_log_le K a (by omega)
  calc (PCPPNative.descriptor Γ).length ≤ 6 * (Γ.size + 1) * (natBitLength (m + Γ.size + 4) + 1) := hd
    _ ≤ 6 * X * ((G * c0 + 3 + G) * natBitLength a) := by gcongr
    _ ≤ 6 * ((2 * C1) ^ G * a ^ G) * ((G * c0 + 3 + G) * natBitLength a) := by gcongr
    _ = a ^ G * (K * natBitLength a) := by rw [hK]; ring
    _ ≤ a ^ G * a := Nat.mul_le_mul_left _ hKa
    _ = a ^ (G + 1) := by ring

end NearCubicWires.WireExponent3_5.Outer35

namespace NearCubicWires.WireExponent3_5.Transfer

open _root_.NearCubicWires _root_.NearCubicWires.RepairRepresentation NearCubicGates.Close

/-- **`lenFit35`** (Lemma H.7(a)): past some `a₀`, every circuit on `q = q(2^a)` inputs within the size cap
`oracleSizeBound (oracleDeg l) q` passes the description-length guard `|⟨Γ⟩| ≤ λ_a = a^{G+1}`. -/
theorem lenFit35 (l : Literals) :
    ∃ a₀ : ℕ, ∀ a, a₀ ≤ a → ∀ Γ : BooleanCircuit (gateWidth l (2 ^ a)),
      Γ.size ≤ _root_.NearCubicWires.RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) (gateWidth l (2 ^ a)) →
        Outer.SrcFits (lenG l) a Γ := by
  obtain ⟨a₀, h⟩ := NearCubicWires.WireExponent3_5.Outer35.lenFit_gen kclk
    (Outer.apad (gateMW l) (gateSV l)) (capExp l) (one_le_capExp l)
  refine ⟨a₀, fun a ha Γ hΓ => ?_⟩
  unfold Outer.SrcFits Outer.srcDescriptor
  rw [instLength_lenG]
  exact h a ha Γ rfl (oracleSize_le l _ _ hΓ)

end NearCubicWires.WireExponent3_5.Transfer
