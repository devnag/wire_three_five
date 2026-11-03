import W3.Front.ColdCaps
import Proof.PCP.PCPPRequestBounds
import Proof.Amplification.RecoveryWitnessPolicy

/-!
# The cold front end, part 5: the meaning of the cold prefix's checks

The guess word `WT` reads like the oracle field (`RdEq`), so its two physical fields are the fields of `raw`
(`fields_of_raw`); a decoded field whose circuit meets the `q^G` cap has a canonical code of at most `L(q)` bits
(`code_bits_le`), so every bit past `L(q)` vanishes and the truncated field has the same value (`trunc_of_decodes`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.Worker.Format (readField readCount countWord)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-- The padded guess word reads like the oracle field. -/
theorem guess_rd (n : ℕ) (raw : List Bool) (h : 16 * raw.length ≤ n) :
    RdEq (guessWord n raw (padB n (n / 16 + 1))) raw := by
  unfold guessWord
  rw [prefixBits_eq, List.take_of_length_le (by omega), List.append_assoc]
  exact rdEq_append_blank _ _ (fun b hb => by
    rcases List.mem_append.1 hb with h1 | h1 <;> exact (List.mem_replicate.1 h1).2)

/-- **The two physical fields** of the padded guess word are the oracle field's. -/
theorem fields_of_raw (n : ℕ) (raw : List Bool) (h : 16 * raw.length ≤ n) :
    ∃ R1 R2 : List Bool, guessWord n raw (padB n (n / 16 + 1)) =
        countWord (readField raw).1.length ++ (readField raw).1 ++ R1 ∧
      R1 = countWord (readField (readField raw).2).1.length ++ (readField (readField raw).2).1 ++ R2 ∧
      (readField raw).1.length ≤ n / 16 ∧ (readField (readField raw).2).1.length ≤ n / 16 := by
  have hrd := guess_rd n raw h
  obtain ⟨e1, r1⟩ := rf_rd hrd
  obtain ⟨s1, h2, h3, -⟩ := guessWord_split n raw (padB n (n / 16 + 1)) (by unfold padB; omega)
  obtain ⟨s2, l2, -⟩ := field2_split n raw (n / 16 + 1) le_rfl
  obtain ⟨e2, -⟩ := rf_rd r1
  refine ⟨(readField (guessWord n raw (padB n (n / 16 + 1)))).2,
    (readField (readField (guessWord n raw (padB n (n / 16 + 1)))).2).2, ?_, ?_, ?_, ?_⟩
  · rw [← e1]; exact s1
  · rw [← e2]; exact s2
  · rw [← e1]; omega
  · rw [← e2]; exact l2

/-- The code of a circuit within the `q^G` cap has at most `L(q)` bits. -/
theorem code_bits_le (degree q : ℕ) (c : BooleanCircuit q)
    (hc : c.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree q) :
    natBitLength (encodeBooleanCircuit c) ≤ Lq (E0 degree) q := by
  have hs := Amplifier.oracleSizeBound_succ degree q
  have hp := RecoveryWitnessPolicy.encodeBooleanCircuit_bits_le_parameter c (parameter := (q + 1) ^ E0 degree + q + 4) (by omega)
    (by omega) (by unfold E0 at *; omega)
  have hb := PCPPRequestBoundary.canonical_circuit_bound ((q + 1) ^ E0 degree + q + 4)
  unfold Lq
  have : (q + 1) ^ E0 degree + q + 4 + 1 = (q + 1) ^ E0 degree + q + 5 := by ring
  rw [this] at hb
  omega

theorem value_lt_of_decode {q : ℕ} (bits : List Bool) (c : BooleanCircuit q)
    (hd : decodeBooleanCircuit q (value bits) = some c) :
    value bits < 2 ^ natBitLength (encodeBooleanCircuit c) := by
  rw [← encodeBooleanCircuit_of_decode hd]
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- **A decoded field within the cap survives truncation**: no `1` past `L(q)`, same value. -/
theorem trunc_of_decodes (degree q : ℕ) (bits : List Bool) (c : BooleanCircuit q)
    (hd : decodeBooleanCircuit q (value bits) = some c)
    (hc : c.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree q) :
    (bits.drop (Lq (E0 degree) q)).count true = 0 ∧
      decodeBooleanCircuit q (value (Codec.prefixBits bits (Lq (E0 degree) q))) = some c := by
  have h1 := value_lt_of_decode bits c hd
  have h2 := code_bits_le degree q c hc
  have h3 : value bits < 2 ^ Lq (E0 degree) q :=
    lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)
  have hz := zero_of_value_lt bits _ h3
  exact ⟨hz, by rw [value_prefix_of_zero bits _ hz]; exact hd⟩

end W3.NearCubicWires.RepairSource.Outer3.Front
