import Proof.Wire_3_5.UnionMachine.FrontWalkRef

/-! # C6 front, U1b: the guess's grid sums, as a list reference (P3:3669-3671)

Realizes the grid-sum part of "one sparse grid sum for each distinct PCPP variable. It rejects malformed descriptions
[...] and coefficients outside the fixed grid" (P3:3669-3671) in the codec: after the oracle field, `V·G` entries
(`encEntry`: the sign `intWord σ`, then the atom's code `natWord c`), variable-major, then zero padding only
(`decodeBody`), with the grid signs `σ ∈ {−1, 0, 1}` checked by `signsOk`.

A grid sign's word is exactly four bits `b 1 0 x` (`intWord σ` with `|σ| ≤ 1`, no negative zero): **`gridInt_iff`**.
So one entry is those four bits and one natural field; `entStep` reads it (the scan of `FrontWalkRef`), `entScan E`
reads `E` entries then checks the zero padding. **`entScan_ok_iff`**: the scan passes exactly when the readers read
`E` grid-valid entries (sign and code, canonical) and the rest is zeros; the codes are the payloads' values
(`value`), the input of the atom decoders. Paper quantity: the guess's grid signs and atom codes. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef

/-- The sign word of a grid value: `b 1 0 x` for `σ = ±x` (`b` the sign bit). -/
def gridWord (b x : Bool) : List Bool := [b, true, false, x]

/-- A grid sign's word is exactly `intWord σ` for `σ ∈ {−1, 0, 1}`, with no negative zero. -/
def gridOK (b x : Bool) : Bool := !(b && !x)

/-- The integer of a grid word. -/
def gridVal (b x : Bool) : ℤ := signedOf b (if x then 1 else 0)

theorem natWord_zero : natWord 0 = [true, false, false] := by decide
theorem natWord_one : natWord 1 = [true, false, true] := by decide

theorem intWord_grid (b x : Bool) (h : gridOK b x = true) : intWord (gridVal b x) = gridWord b x := by
  cases b <;> cases x <;> simp_all [gridOK, gridVal, gridWord, signedOf, intWord, natWord_zero, natWord_one]

/-- **The grid words are exactly the words of grid integers.** `readInt` reads `σ ∈ {−1,0,1}` off `u` iff `u` starts
with a grid word. -/
theorem gridInt_iff (u : List Bool) (z : ℤ) (r : List Bool) :
    (readInt u = some (z, r) ∧ z ∈ ({-1, 0, 1} : Finset ℤ)) ↔
      ∃ b x, gridOK b x = true ∧ u = gridWord b x ++ r ∧ z = gridVal b x := by
  constructor
  · rintro ⟨h, hz⟩
    have e := readInt_sound h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · refine ⟨true, true, rfl, ?_, rfl⟩; rw [e]; simp [intWord, gridWord, natWord_one]
    · refine ⟨false, false, rfl, ?_, rfl⟩; rw [e]; simp [intWord, gridWord, natWord_zero]
    · refine ⟨false, true, rfl, ?_, rfl⟩; rw [e]; simp [intWord, gridWord, natWord_one]
  · rintro ⟨b, x, hok, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← intWord_grid b x hok]; exact readInt_intWord _ r
    · cases b <;> cases x <;> simp_all [gridOK, gridVal, signedOf]

/-- One entry read off `u`: the grid word, then the atom field (scanned); `none` when malformed. The result: the
sign bits, the code's payload, the rest. -/
def entStep (u : List Bool) : Option ((Bool × Bool) × List Bool × List Bool) :=
  match u with
  | b :: true :: false :: x :: t =>
      if gridOK b x && scanOK t then some ((b, x), payload t, restOf t) else none
  | _ => none

/-- `E` entries, then the zero padding: the verdict, the signs and the payloads (on a pass). -/
def entScan : ℕ → List Bool → Option (List (Bool × Bool) × List (List Bool))
  | 0, u => if u.all (fun b => !b) then some ([], []) else none
  | E + 1, u => (entStep u).bind fun e => (entScan E e.2.2).map fun r => (e.1 :: r.1, e.2.1 :: r.2)

/-- The scan's verdict against the readers: an entry passes exactly when `readInt` reads a grid sign and `readNat`
reads a code after it. -/
theorem entStep_iff (u : List Bool) :
    (entStep u).isSome = true ↔ ∃ z r v r', readInt u = some (z, r) ∧ z ∈ ({-1, 0, 1} : Finset ℤ) ∧
      readNat r = some (v, r') := by
  constructor
  · intro h
    obtain ⟨⟨s, p, r⟩, hs⟩ := Option.isSome_iff_exists.1 h
    match u, hs with
    | b :: true :: false :: x :: t, hs =>
      simp only [entStep] at hs
      split_ifs at hs with hc
      simp only [Bool.and_eq_true] at hc
      have hg := (gridInt_iff (b :: true :: false :: x :: t) (gridVal b x) t).2 ⟨b, x, hc.1, rfl, rfl⟩
      exact ⟨_, t, _, _, hg.1, hg.2, readNat_of_scan t hc.2⟩
  · rintro ⟨z, r, v, r', hz, hmem, hv⟩
    obtain ⟨b, x, hok, rfl, rfl⟩ := (gridInt_iff u z r).1 ⟨hz, hmem⟩
    have hs : scanOK r = true := by
      have := readNat_isSome r; rw [hv] at this; simpa using this.symm
    simp [entStep, gridWord, hok, hs]

/-- The sign word test: `b 1 0 x`, a grid value. -/
def sgnOK' : List Bool → Bool
  | b :: true :: false :: x :: _ => gridOK b x
  | _ => false

/-- The rest after `n` entries (`none` on a malformed entry). -/
def restAfter : ℕ → List Bool → Option (List Bool)
  | 0, u => some u
  | n + 1, u => (entStep u).bind fun e => restAfter n e.2.2

theorem entScan_isSome (E : ℕ) (u : List Bool) :
    (entScan E u).isSome = match restAfter E u with | none => false | some r => r.all (fun b => !b) := by
  induction E generalizing u with
  | zero => simp only [entScan, restAfter]; split_ifs with h <;> simp [h]
  | succ E ih =>
    simp only [entScan, restAfter]
    cases h : entStep u with
    | none => rfl
    | some e => simp [ih]

/-- The sign word test and the field scan decide an entry. -/
theorem entStep_isSome (u : List Bool) :
    (entStep u).isSome = (FrontEntriesRef.sgnOK' u && scanOK (u.drop 4)) := by
  match u with
  | [] => rfl
  | [_] => rfl
  | [_, x] => cases x <;> rfl
  | [_, x, y] => cases x <;> cases y <;> rfl
  | b :: x :: y :: z :: t =>
    cases x <;> cases y <;> simp [entStep, sgnOK']
    split_ifs <;> simp_all

/-- A passing entry's rest: past the sign word and the field. -/
theorem entStep_rest (u : List Bool) (s : Bool × Bool) (p r : List Bool) (h : entStep u = some (s, p, r)) :
    r = (u.drop 4).drop (2 * ones (u.drop 4) + 1) ∧ 2 * ones (u.drop 4) + 1 ≤ (u.drop 4).length := by
  match u, h with
  | b :: true :: false :: x :: t, h =>
    simp only [entStep] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    have := hc.2
    simp only [scanOK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨rfl, this.1.2⟩

theorem restAfter_add (a b : ℕ) (u : List Bool) : restAfter (a + b) u = (restAfter a u).bind (restAfter b) := by
  induction a generalizing u with
  | zero => simp [restAfter]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [restAfter]
    cases entStep u with
    | none => rfl
    | some e => simp [ih]

/-- The rest after one more entry. -/
theorem restAfter_succ' (j : ℕ) (u : List Bool) :
    restAfter (j + 1) u = (restAfter j u).bind fun v => (entStep v).map fun e => e.2.2 := by
  rw [restAfter_add]
  congr 1
  funext v
  simp only [restAfter]
  cases entStep v <;> rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef
