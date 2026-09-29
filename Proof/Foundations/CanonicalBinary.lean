import Proof.Foundations.CanonicalBalanced

/-!
# Canonical structural binary syntax

The weak register machine has pairing, unpairing, and zero tests, but no
primitive integer arithmetic or trusted decoder opcode.  This module therefore
owns the one raw syntax used at executable validation boundaries: lists are
zero terminated, every nonempty node has the exact tag `1`, and integers are
canonical little-endian bit lists.  Partial decoders reject malformed tags,
non-bits, negative zero, and noncanonical high zeroes.

The definitions are intentionally independent of any circuit family.  Gate,
Fourfold, legal-sum, and recovery-witness codecs share these primitives rather
than maintaining family-specific numeric encodings.
-/

namespace NearCubicWires.CanonicalBinary

open NearCubicWires

/-! ## A finite machine signature for the constructor tag -/

/-! ## Structural lists and unary control data -/


def decodeTaggedListAux : ℕ → ℕ → Option (List ℕ)
  | 0, code => if code = 0 then some [] else none
  | fuel + 1, code =>
      if code = 0 then
        some []
      else
        let outer := Nat.unpair code
        if outer.1 = 1 then
          let payload := Nat.unpair outer.2
          (decodeTaggedListAux fuel payload.2).map (payload.1 :: ·)
        else
          none

/-- The code itself is a sufficient termination bound: each valid cell is at
least one larger than its remaining list. -/
def decodeTaggedListCandidate (code : ℕ) : Option (List ℕ) :=
  decodeTaggedListAux code code

theorem encodeTaggedList_length_le (values : List ℕ) :
    values.length ≤ encodeTaggedList values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.length_cons, encodeTaggedList]
      have hinner :
          encodeTaggedList rest ≤
            Nat.pair value (encodeTaggedList rest) :=
        Nat.right_le_pair value (encodeTaggedList rest)
      have houter :=
        Nat.add_le_pair 1
          (Nat.pair value (encodeTaggedList rest))
      omega

theorem decodeTaggedListAux_encode
    (values : List ℕ) (fuel : ℕ) (hfuel : values.length ≤ fuel) :
    decodeTaggedListAux fuel (encodeTaggedList values) = some values := by
  induction values generalizing fuel with
  | nil =>
      cases fuel <;> rfl
  | cons value rest ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hnonzero :
              Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) ≠ 0 := by
            have hleft :=
              Nat.left_le_pair 1
                (Nat.pair value (encodeTaggedList rest))
            omega
          simp only [encodeTaggedList, decodeTaggedListAux,
            if_neg hnonzero, Nat.unpair_pair]
          rw [if_pos trivial]
          rw [ih fuel (by simpa using hfuel)]
          rfl

@[simp] theorem decodeTaggedListCandidate_encode (values : List ℕ) :
    decodeTaggedListCandidate (encodeTaggedList values) = some values := by
  unfold decodeTaggedListCandidate
  exact decodeTaggedListAux_encode values
    (encodeTaggedList values) (encodeTaggedList_length_le values)

/-- Exact re-encoding turns the structural parser into a canonical codec. -/
def decodeTaggedList (code : ℕ) : Option (List ℕ) := do
  let values ← decodeTaggedListCandidate code
  if encodeTaggedList values = code then some values else none

@[simp] theorem decodeTaggedList_encode (values : List ℕ) :
    decodeTaggedList (encodeTaggedList values) = some values := by
  unfold decodeTaggedList
  rw [decodeTaggedListCandidate_encode]
  simp

theorem encodeTaggedList_of_decode
    {code : ℕ} {values : List ℕ}
    (hdecode : decodeTaggedList code = some values) :
    encodeTaggedList values = code := by
  unfold decodeTaggedList at hdecode
  generalize hcandidate :
    decodeTaggedListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if encodeTaggedList decoded = code then some decoded else none) =
          some values at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

/-! ## Canonical finite binary integers -/


def decodeBoolCode (code : ℕ) : Option Bool :=
  if code = 0 then some false
  else if code = 1 then some true
  else none

@[simp] theorem decodeBoolCode_boolCode (value : Bool) :
    decodeBoolCode (boolCode value) = some value := by
  cases value <;> rfl

def decodeBoolCodes : List ℕ → Option (List Bool)
  | [] => some []
  | code :: codes => do
      let value ← decodeBoolCode code
      let values ← decodeBoolCodes codes
      pure (value :: values)

@[simp] theorem decodeBoolCodes_map_boolCode (values : List Bool) :
    decodeBoolCodes (values.map boolCode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [decodeBoolCodes, ih]


def decodeBoolListCandidate (code : ℕ) : Option (List Bool) := do
  let raw ← decodeBalancedList code
  decodeBoolCodes raw

/-- Boolean vectors do not impose a high-bit convention; their length is
provided by the surrounding typed circuit. -/
def decodeBoolList (code : ℕ) : Option (List Bool) :=
  (decodeBoolListCandidate code).bind fun values =>
    if encodeBoolList values = code then some values else none

@[simp] theorem decodeBoolList_encode (values : List Bool) :
    decodeBoolList (encodeBoolList values) = some values := by
  have hcandidate :
      decodeBoolListCandidate (encodeBoolList values) = some values := by
    unfold decodeBoolListCandidate encodeBoolList
    rw [decodeBalancedList_encode]
    exact decodeBoolCodes_map_boolCode values
  unfold decodeBoolList
  rw [hcandidate]
  simp

theorem encodeBoolList_of_decode
    {code : ℕ} {values : List Bool}
    (hdecode : decodeBoolList code = some values) :
    encodeBoolList values = code := by
  unfold decodeBoolList at hdecode
  generalize hcandidate :
    decodeBoolListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode


def decodeBitsCandidate (code : ℕ) : Option (List Bool) :=
  decodeBoolList code

/-- A bit list is canonical when it is empty or its most significant bit is
`true`.  Exact re-encoding also rules out every alternate structural code. -/
def decodeBits (code : ℕ) : Option (List Bool) := do
  let values ← decodeBitsCandidate code
  if values = [] ∨ values.getLast? = some true then
    if encodeBits values = code then some values else none
  else
    none

theorem Nat.bits_canonical (value : ℕ) :
    value.bits = [] ∨ value.bits.getLast? = some true := by
  induction value using Nat.binaryRec' with
  | zero => exact Or.inl rfl
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue]
      cases hbits : value.bits with
      | nil =>
          have hvalueZero : value = 0 := by
            have hlength :
                value.bits.length = value.size :=
              Nat.size_eq_bits_len value
            rw [hbits] at hlength
            exact Nat.size_eq_zero.mp (by simpa using hlength.symm)
          have hbit : bit = true := hvalue hvalueZero
          subst bit
          simp
      | cons head tail =>
          right
          rcases ih with hempty | hlast
          · simp [hbits] at hempty
          · simpa [hbits] using hlast

@[simp] theorem decodeBits_encode_natBits (value : ℕ) :
    decodeBits (encodeBits value.bits) = some value.bits := by
  have hcandidate :
      decodeBitsCandidate (encodeBits value.bits) = some value.bits := by
    exact decodeBoolList_encode value.bits
  unfold decodeBits
  rw [hcandidate]
  change
    (if value.bits = [] ∨ value.bits.getLast? = some true then
      if encodeBits value.bits = encodeBits value.bits then
        some value.bits
      else none
    else none) = some value.bits
  rw [if_pos (Nat.bits_canonical value)]
  rw [if_pos rfl]


theorem bitsValue_natBits (value : ℕ) :
    bitsValue value.bits = value := by
  induction value using Nat.binaryRec' with
  | zero => rfl
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue]
      simp only [bitsValue, ih]
      cases bit
      · simp [Nat.bit]
      · simp [Nat.bit]
        omega


/-- Polynomial register-width charge for the total `encodeNat` machine
instruction. -/
def encodeNatBitsBound (sourceBits : ℕ) : ℕ :=
  1 + 2 * sourceBits ^ 4 * (sourceBits + 1)

theorem encodeNat_bits_le (value : ℕ) :
    natBitLength (encodeNat value) ≤
      encodeNatBitsBound (natBitLength value) := by
  have hlength : value.bits.length ≤ natBitLength value := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    simpa [natBitLength, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) value)
  have hboolBits (bit : Bool) :
      natBitLength (boolCode bit) = 1 := by
    cases bit <;> rfl
  have hsum (bits : List Bool) :
      (bits.map (natBitLength ∘ boolCode)).sum = bits.length := by
    induction bits with
    | nil => rfl
    | cons bit bits ih =>
        simp [hboolBits, ih, Nat.add_comm]
  have hatom :
      balancedListAtomBits (value.bits.map boolCode) =
        value.bits.length + 1 := by
    unfold balancedListAtomBits
    rw [List.map_map, hsum]
  calc
    natBitLength (encodeNat value) ≤
        1 + 2 * value.bits.length ^ 4 *
          balancedListAtomBits (value.bits.map boolCode) := by
      simpa [encodeNat, encodeBits, encodeBoolList] using
        balancedListCodeBits_le (value.bits.map boolCode)
    _ = 1 + 2 * value.bits.length ^ 4 *
          (value.bits.length + 1) := by rw [hatom]
    _ ≤ encodeNatBitsBound (natBitLength value) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlength 4)
      · exact Nat.add_le_add_right hlength 1

def decodeNat (code : ℕ) : Option ℕ := do
  let bits ← decodeBits code
  let value := bitsValue bits
  if encodeNat value = code then some value else none

@[simp] theorem decodeNat_encode (value : ℕ) :
    decodeNat (encodeNat value) = some value := by
  unfold decodeNat encodeNat
  rw [decodeBits_encode_natBits]
  change
    (if encodeNat (bitsValue value.bits) = encodeBits value.bits then
      some (bitsValue value.bits)
    else none) = some value
  rw [bitsValue_natBits]
  simp [encodeNat]

theorem encodeNat_of_decode
    {code value : ℕ} (hdecode : decodeNat code = some value) :
    encodeNat value = code := by
  unfold decodeNat at hdecode
  generalize hbits : decodeBits code = bitsOption at hdecode
  cases bitsOption with
  | none => simp at hdecode
  | some bits =>
      change
        (if encodeNat (bitsValue bits) = code then
          some (bitsValue bits)
        else none) = some value at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst value
        exact hcanonical
      · simp at hdecode

def encodeInt (value : ℤ) : ℕ :=
  Nat.pair (if value < 0 then 1 else 0) (encodeNat value.natAbs)

def decodeIntCandidate (code : ℕ) : Option ℤ := do
  let sign ← decodeBoolCode (Nat.unpair code).1
  let magnitude ← decodeNat (Nat.unpair code).2
  if sign ∧ magnitude = 0 then
    none
  else
    pure (if sign then -(magnitude : ℤ) else (magnitude : ℤ))

def decodeInt (code : ℕ) : Option ℤ := do
  let value ← decodeIntCandidate code
  if encodeInt value = code then some value else none

theorem encodeInt_of_decode
    {code : ℕ} {value : ℤ}
    (hdecode : decodeInt code = some value) :
    encodeInt value = code := by
  unfold decodeInt at hdecode
  generalize hcandidate : decodeIntCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      change
        (if encodeInt decoded = code then some decoded else none) =
          some value at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst decoded
        exact hcanonical
      · simp at hdecode

@[simp] theorem decodeInt_encode (value : ℤ) :
    decodeInt (encodeInt value) = some value := by
  unfold decodeInt decodeIntCandidate encodeInt
  rw [Nat.unpair_pair]
  dsimp only
  cases value with
  | ofNat magnitude =>
      simp [decodeBoolCode]
  | negSucc magnitude =>
      have hrepr :
          -1 + -(magnitude : ℤ) = Int.negSucc magnitude := by
        omega
      simp [decodeBoolCode, hrepr]

/-! ## Canonical lists of binary atoms -/

def encodeIntList (values : List ℤ) : ℕ :=
  encodeBalancedList (values.map encodeInt)

def decodeIntCodes : List ℕ → Option (List ℤ)
  | [] => some []
  | code :: codes => do
      let value ← decodeInt code
      let values ← decodeIntCodes codes
      pure (value :: values)

def decodeIntListCandidate (code : ℕ) : Option (List ℤ) := do
  let codes ← decodeBalancedList code
  decodeIntCodes codes

def decodeIntList (code : ℕ) : Option (List ℤ) :=
  (decodeIntListCandidate code).bind fun values =>
    if encodeIntList values = code then some values else none

@[simp] theorem decodeIntCodes_map_encodeInt (values : List ℤ) :
    decodeIntCodes (values.map encodeInt) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [decodeIntCodes, ih]

@[simp] theorem decodeIntList_encode (values : List ℤ) :
    decodeIntList (encodeIntList values) = some values := by
  have hcandidate :
      decodeIntListCandidate (encodeIntList values) = some values := by
    unfold decodeIntListCandidate encodeIntList
    rw [decodeBalancedList_encode]
    exact decodeIntCodes_map_encodeInt values
  unfold decodeIntList
  rw [hcandidate]
  simp

theorem encodeIntList_of_decode
    {code : ℕ} {values : List ℤ}
    (hdecode : decodeIntList code = some values) :
    encodeIntList values = code := by
  unfold decodeIntList at hdecode
  generalize hcandidate :
    decodeIntListCandidate code = candidate at hdecode
  cases candidate with
  | none => simp at hdecode
  | some decoded =>
      simp only [Option.bind_some] at hdecode
      split at hdecode
      · rename_i hcanonical
        simp only [Option.some.injEq] at hdecode
        subst values
        exact hcanonical
      · simp at hdecode

/-! ## Shared binary arithmetic certificates -/

end NearCubicWires.CanonicalBinary
