import Proof.Wire_3_5.UnionMachine.RoundBits

/-! # C6 front, U1a: the oracle field of the guess, as a list reference (P3:3669-3671)

Realizes the first field of "The weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid
sum for each distinct PCPP variable" (P3:3669-3671) in the codec (`UnionGuess.word`: the tag bit, then
`natWord (encodeBooleanCircuit oracle)`; `decodeGuess`, which reads the field with `readNat`, canonical form only):
the reference the front's walker computes.

* the scan of a word `t`: `k = ones t` leading ones, the separator, the payload `payload t` (the next `k` bits), the
  rest `restOf t = t.drop (2k+1)`, and the verdict `scanOK t` (`k ≥ 1`, `2k+1 ≤ |t|`, the payload's last bit is `1`
  unless `k = 1`);
* **`readNat_of_scan`**: on a passing scan, `readNat t = some (value (payload t), restOf t)`;
* **`scan_of_readNat`**: `readNat` succeeds only on a passing scan; hence **`readNat_isSome`**.

The payload is the oracle's code in binary (low bit first), whose `value` (`RadixSemantics.value`) is the code: the
input of the Theorem 2.5 repository's cold oracle decoder (`CloseoutWitness.Oracle.cold_run`, `decodeBooleanCircuit (value arityBits)
(value bits)`). Paper quantity: the guess's oracle field (its code) and the rest of the guess. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.UnionMachine.Round

/-! ## The scan -/

/-- The leading-ones count of a word. -/
def ones (w : List Bool) : ℕ := (countOnes w).1

theorem ones_cons_true (w : List Bool) : ones (true :: w) = ones w + 1 := rfl
theorem ones_cons_false (w : List Bool) : ones (false :: w) = 0 := rfl
theorem ones_nil : ones [] = 0 := rfl

theorem ones_le : ∀ w : List Bool, ones w ≤ w.length
  | [] => le_rfl
  | false :: w => Nat.zero_le _
  | true :: w => by rw [ones_cons_true]; have := ones_le w; simp; omega

/-- The leading ones. -/
theorem ones_take : ∀ w : List Bool, w.take (ones w) = List.replicate (ones w) true
  | [] => rfl
  | false :: w => rfl
  | true :: w => by rw [ones_cons_true, List.take_succ_cons, ones_take w]; rfl

/-- The bit after the leading ones, when there is one, is `0`. -/
theorem ones_stop : ∀ w : List Bool, ones w < w.length → w.getD (ones w) true = false
  | [] => fun h => absurd h (by simp [ones_nil])
  | false :: w => fun _ => rfl
  | true :: w => fun h => by
    rw [ones_cons_true] at h ⊢
    simp only [List.length_cons] at h
    simpa using ones_stop w (by omega)

/-- The leading ones of a word that starts with `1^k 0`. -/
theorem ones_rep (k : ℕ) (t : List Bool) : ones (List.replicate k true ++ false :: t) = k := by
  unfold ones; rw [countOnes_replicate]

/-- The payload: the `k` bits after the separator. -/
def payload (t : List Bool) : List Bool := (t.drop (ones t + 1)).take (ones t)

/-- The rest of the word after the field. -/
def restOf (t : List Bool) : List Bool := t.drop (2 * ones t + 1)

/-- **The scan's verdict**: `k ≥ 1` ones, then `0`, then `k` bits, the last of them `1` unless `k = 1`. -/
def scanOK (t : List Bool) : Bool :=
  decide (1 ≤ ones t) && decide (2 * ones t + 1 ≤ t.length) && (decide (ones t = 1) || t.getD (2 * ones t) false)

theorem payload_length (t : List Bool) (h : 2 * ones t + 1 ≤ t.length) : (payload t).length = ones t := by
  simp [payload]; omega

/-- The word, cut at its field. -/
theorem decomp (t : List Bool) (h : ones t < t.length) :
    t = List.replicate (ones t) true ++ false :: (payload t ++ restOf t) := by
  have h1 : t = t.take (ones t) ++ t.drop (ones t) := (List.take_append_drop _ _).symm
  have h2 : t.drop (ones t) = false :: t.drop (ones t + 1) := by
    have hs := ones_stop t h
    rw [List.drop_eq_getElem_cons h]
    congr 1
    rw [List.getD_eq_getElem _ _ h] at hs
    exact hs
  have h3 : t.drop (ones t + 1) = payload t ++ restOf t := by
    unfold payload restOf
    have e : t.drop (2 * ones t + 1) = (t.drop (ones t + 1)).drop (ones t) := by
      rw [List.drop_drop]; congr 1; omega
    rw [e, List.take_append_drop]
  conv_lhs => rw [h1, h2, h3, ones_take t]

/-! ## Canonical naturals -/

/-- A bit list of length `k ≥ 1` whose last bit is `1` (or `k = 1`) is the canonical binary of its value. -/
theorem natBitLength_value (bs : List Bool) (hk : 1 ≤ bs.length)
    (hlast : bs.length = 1 ∨ bs.getD (bs.length - 1) false = true) : natBitLength (value bs) = bs.length := by
  unfold natBitLength
  have hlt := value_lt bs
  rcases hlast with h1 | hl
  · have : value bs < 2 := by rw [h1] at hlt; simpa using hlt
    rw [h1]
    interval_cases (value bs) <;> simp
  · obtain ⟨init, b, rfl⟩ : ∃ init b, bs = init ++ [b] := by
      refine ⟨bs.dropLast, bs.getLast (by intro h; simp [h] at hk), ?_⟩
      exact (List.dropLast_append_getLast _).symm
    have hb : b = true := by simpa using hl
    subst hb
    rw [value_append] at hlt ⊢
    simp only [value, Bool.toNat_true, List.length_append, List.length_singleton] at hlt ⊢
    have hi := value_lt init
    have hlo : 2 ^ init.length ≤ value init + 2 ^ init.length * (1 + 2 * 0) := by omega
    rw [Nat.log_eq_of_pow_le_of_lt_pow hlo (by rw [pow_succ]; omega)]

theorem natWord_value (bs : List Bool) (hk : 1 ≤ bs.length)
    (hlast : bs.length = 1 ∨ bs.getD (bs.length - 1) false = true) :
    natWord (value bs) = List.replicate bs.length true ++ false :: bs := by
  rw [natWord_eq, natBitLength_value bs hk hlast, RepairSource.VerifierDecoding.binary_value_word]

/-- The last bit of the canonical binary of `v ≥ 1` is `1`. -/
theorem binary_last (v : ℕ) (hv : 1 ≤ v) :
    (binary (natBitLength v) v).getD (natBitLength v - 1) false = true := by
  have hb : ∀ (w n : ℕ), 1 ≤ w → 2 ^ (w - 1) ≤ n → n < 2 ^ w → (binary w n).getD (w - 1) false = true := by
    intro w
    induction w with
    | zero => intro n h; omega
    | succ w ih =>
      intro n _ hlo hhi
      rw [binary_succ]
      rcases Nat.eq_zero_or_pos w with hw | hw
      · subst hw
        simp at hlo hhi ⊢
        omega
      · have hlo' : 2 ^ (w - 1) ≤ n / 2 := by
          rw [Nat.le_div_iff_mul_le (by norm_num)]
          have e : 2 ^ (w + 1 - 1) = 2 ^ (w - 1) * 2 := by
            rw [show w + 1 - 1 = (w - 1) + 1 by omega, pow_succ]
          omega
        have hhi' : n / 2 < 2 ^ w := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hhi; omega
        have := ih (n / 2) hw hlo' hhi'
        rw [show w + 1 - 1 = (w - 1) + 1 by omega]
        simpa using this
  apply hb _ v (by unfold natBitLength; omega)
  · unfold natBitLength
    simpa using Nat.pow_log_le_self 2 (by omega : v ≠ 0)
  · exact natBitLength_lt v

/-! ## The reader and the scan -/

theorem payload_last (t : List Bool) (h1 : 1 ≤ ones t) (h2 : 2 * ones t + 1 ≤ t.length) :
    (payload t).getD ((payload t).length - 1) false = t.getD (2 * ones t) false := by
  rw [payload_length t h2]
  unfold payload
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- **On a passing scan the reader returns the payload's value and the rest.** -/
theorem readNat_of_scan (t : List Bool) (h : scanOK t = true) :
    readNat t = some (value (payload t), restOf t) := by
  simp only [scanOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hlen := payload_length t h2
  have hw : natWord (value (payload t)) = List.replicate (ones t) true ++ false :: payload t := by
    rw [natWord_value (payload t) (by omega) ?_, hlen]
    rcases h3 with h3 | h3
    · left; omega
    · right; rw [payload_last t h1 h2]; exact h3
  have e : t = natWord (value (payload t)) ++ restOf t := by
    rw [hw]
    simpa using decomp t (by omega)
  have := readNat_natWord (value (payload t)) (restOf t)
  rw [← e] at this
  exact this

/-- **The reader succeeds only on a passing scan.** -/
theorem scan_of_readNat (t : List Bool) (v : ℕ) (r : List Bool) (h : readNat t = some (v, r)) : scanOK t = true := by
  have e := readNat_sound h
  have hk : ones t = natBitLength v := by
    rw [e, natWord_eq, List.append_assoc, List.cons_append, ones_rep]
  have hL : t.length = 2 * natBitLength v + 1 + r.length := by
    rw [e, natWord_eq]; simp [binary_length]; omega
  have hpos : 1 ≤ natBitLength v := by unfold natBitLength; omega
  simp only [scanOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  by_cases h1 : natBitLength v = 1
  · left; omega
  · right
    have hv : 1 ≤ v := by
      by_contra h0
      have : v = 0 := by omega
      subst this
      exact h1 rfl
    rw [hk, e, natWord_eq, List.append_assoc, List.cons_append]
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_replicate]
    rw [show 2 * natBitLength v - natBitLength v = (natBitLength v - 1) + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp [binary_length]; omega)]
    exact binary_last v hv

/-- **The canonical reader succeeds exactly on a passing scan.** -/
theorem readNat_isSome (t : List Bool) : (readNat t).isSome = scanOK t := by
  cases h : scanOK t with
  | true => rw [readNat_of_scan t h]; rfl
  | false =>
    cases hr : readNat t with
    | none => rfl
    | some p =>
      obtain ⟨v, r⟩ := p
      rw [scan_of_readNat t v r hr] at h
      exact absurd h (by decide)



end NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef
