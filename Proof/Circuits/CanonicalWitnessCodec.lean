import Proof.Foundations.SupplierPipeline

/-!
# Canonical raw-witness codecs

The weak-machine witness is an untrusted natural number.  This module provides
the single boundary from that number to the two normalized circuit families
used by the fourfold suppliers.  Every decoder is partial, validates all
shape/resource predicates before constructing a typed value, and finally
checks exact re-encoding.  There is deliberately no default value for malformed
syntax and no alternate raw encoding.
-/

namespace NearCubicWires.CanonicalWitnessCodec

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SupplierPipeline

abbrev CircuitFamily := NearCubicWires.SupplierPipeline.CircuitFamily

/-- A dependent codec is canonical in both directions: typed values always
decode, and every successful raw decode re-encodes to its exact input. -/
structure CanonicalCircuitCodec (Circuit : CircuitFamily) where
  encode : {n : ℕ} → Circuit n → ℕ
  decode : (n code : ℕ) → Option (Circuit n)
  decode_encode : ∀ {n : ℕ} (circuit : Circuit n),
    decode n (encode circuit) = some circuit
  encode_decode : ∀ {n code : ℕ} {circuit : Circuit n},
    decode n code = some circuit → encode circuit = code

theorem CanonicalCircuitCodec.decode_isSome_iff_exists_encode
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (n code : ℕ) :
    (codec.decode n code).isSome ↔
      ∃ value : Circuit n, codec.encode value = code := by
  constructor
  · rw [Option.isSome_iff_exists]
    rintro ⟨value, hdecode⟩
    exact ⟨value, codec.encode_decode hdecode⟩
  · rintro ⟨value, rfl⟩
    exact Option.isSome_iff_exists.2
      ⟨value, codec.decode_encode value⟩

private def listFunction {α : Type} {n : ℕ} (values : List α)
    (hlength : values.length = n) : Fin n → α :=
  fun index =>
    values.get ⟨index.val, by omega⟩

private theorem listFunction_ofFn {α : Type} {n : ℕ}
    (values : Fin n → α) :
    listFunction (List.ofFn values) (by simp) = values := by
  funext index
  simp [listFunction]

private theorem ofFn_listFunction
    {α : Type} {n : ℕ} (values : List α)
    (hlength : values.length = n) :
    List.ofFn (listFunction values hlength) = values := by
  apply List.ext_get
  · simp [hlength]
  · intro index hleft hright
    simp [listFunction]

private theorem ofFn_supportList
    {n : ℕ} (membership : List Bool)
    (hlength : membership.length = n) :
    List.ofFn
        (fun index : Fin n =>
          decide
            (index ∈
              Finset.univ.filter fun candidate =>
                listFunction membership hlength candidate = true)) =
      membership := by
  subst n
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.get_ofFn, Finset.mem_filter, Finset.mem_univ, true_and]
    change
      decide
          (listFunction membership (by rfl) ⟨index, by omega⟩ = true) =
        membership.get ⟨index, hright⟩
    have hget :
        listFunction membership (by rfl) ⟨index, by omega⟩ =
          membership.get ⟨index, hright⟩ := by
      rfl
    rw [hget]
    cases membership.get ⟨index, hright⟩ <;> decide

private def supportedGateFromLists (n : ℕ)
    (weights : List ℤ) (threshold : ℤ) (membership : List Bool)
    (hweights : weights.length = n)
    (hmembership : membership.length = n)
    (hzero : ∀ index : Fin n,
      listFunction membership hmembership index = false →
      listFunction weights hweights index = 0) :
    SupportedNormalizedGate n where
  gate :=
    { weight := listFunction weights hweights
      threshold := threshold }
  support :=
    Finset.univ.filter fun index =>
      listFunction membership hmembership index = true
  zeroOutside := by
    intro index hindex
    apply hzero index
    cases hvalue : listFunction membership hmembership index
    · rfl
    · exact False.elim (hindex (by simp [hvalue]))

private theorem encode_supportedGateFromLists
    (n : ℕ) (weights : List ℤ) (threshold : ℤ)
    (membership : List Bool)
    (hweights : weights.length = n)
    (hmembership : membership.length = n)
    (hzero : ∀ index : Fin n,
      listFunction membership hmembership index = false →
      listFunction weights hweights index = 0) :
    encodeSupportedNormalizedGate
        (supportedGateFromLists n weights threshold membership
          hweights hmembership hzero) =
      encodeTaggedList
        [encodeIntList weights, encodeInt threshold,
          encodeBoolList membership] := by
  unfold encodeSupportedNormalizedGate supportedGateFromLists
  simp only [ofFn_listFunction, ofFn_supportList]

private def decodeSupportedNormalizedGateCandidate
    (n code : ℕ) : Option (SupportedNormalizedGate n) :=
  match decodeTaggedList code with
  | some [weightsCode, thresholdCode, membershipCode] =>
      match decodeIntList weightsCode, decodeInt thresholdCode,
          decodeBoolList membershipCode with
      | some weights, some threshold, some membership =>
          if hweights : weights.length = n then
            if hmembership : membership.length = n then
              if hzero : ∀ index : Fin n,
                  listFunction membership hmembership index = false →
                  listFunction weights hweights index = 0 then
                some (supportedGateFromLists n weights threshold membership
                  hweights hmembership hzero)
              else none
            else none
          else none
      | _, _, _ => none
  | _ => none

/-- Decode one normalized gate and reject any malformed or noncanonical code. -/
def decodeSupportedNormalizedGate
    (n code : ℕ) : Option (SupportedNormalizedGate n) :=
  (decodeSupportedNormalizedGateCandidate n code).bind fun gate =>
    if encodeSupportedNormalizedGate gate = code then some gate else none

theorem encodeSupportedNormalizedGate_of_decode
    {n code : ℕ} {gate : SupportedNormalizedGate n}
    (hdecode : decodeSupportedNormalizedGate n code = some gate) :
    encodeSupportedNormalizedGate gate = code := by
  unfold decodeSupportedNormalizedGate at hdecode
  generalize hcandidate :
    decodeSupportedNormalizedGateCandidate n code = candidate at hdecode
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

private theorem supportedGateFromCanonicalLists
    {n : ℕ} (gate : SupportedNormalizedGate n)
    (hzero : ∀ index : Fin n,
      listFunction
          (List.ofFn fun index : Fin n => decide (index ∈ gate.support))
          (by simp) index = false →
        listFunction (List.ofFn gate.gate.weight) (by simp) index = 0) :
    supportedGateFromLists n (List.ofFn gate.gate.weight)
      gate.gate.threshold
      (List.ofFn fun index : Fin n => decide (index ∈ gate.support))
      (by simp) (by simp) hzero = gate := by
  cases gate with
  | mk raw support zeroOutside =>
      simp only [supportedGateFromLists, SupportedNormalizedGate.mk.injEq]
      constructor
      · cases raw
        congr
        exact listFunction_ofFn _
      · ext index
        simp [listFunction_ofFn]

private theorem canonicalMembership_zero
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    ∀ index : Fin n,
      listFunction
          (List.ofFn fun index : Fin n => decide (index ∈ gate.support))
          (by simp) index = false →
        listFunction (List.ofFn gate.gate.weight) (by simp) index = 0 := by
  intro index hfalse
  rw [listFunction_ofFn] at hfalse ⊢
  apply gate.zeroOutside index
  simpa using hfalse

theorem decodeSupportedNormalizedGate_encode
    {n : ℕ} (gate : SupportedNormalizedGate n) :
    decodeSupportedNormalizedGate n
      (encodeSupportedNormalizedGate gate) = some gate := by
  unfold decodeSupportedNormalizedGate
  unfold decodeSupportedNormalizedGateCandidate
  unfold encodeSupportedNormalizedGate
  rw [decodeTaggedList_encode]
  dsimp only
  rw [decodeIntList_encode, decodeInt_encode, decodeBoolList_encode]
  simp only [List.length_ofFn]
  simp only [dif_pos True.intro]
  rw [dif_pos (canonicalMembership_zero gate)]
  simp only [Option.bind_some]
  rw [supportedGateFromCanonicalLists]
  simp

/-- The one canonical codec for normalized threshold gates. -/
def supportedGateCodec : CanonicalCircuitCodec SupportedNormalizedGate where
  encode := encodeSupportedNormalizedGate
  decode := decodeSupportedNormalizedGate
  decode_encode := decodeSupportedNormalizedGate_encode
  encode_decode := by
    intro n code gate hdecode
    exact encodeSupportedNormalizedGate_of_decode hdecode

theorem decodeSupportedNormalizedGate_isSome_iff_fields
    (n raw : ℕ) :
    (decodeSupportedNormalizedGate n raw).isSome ↔
      ∃ weightsCode thresholdCode membershipCode weights threshold membership,
        decodeTaggedList raw =
            some [weightsCode, thresholdCode, membershipCode] ∧
          decodeIntList weightsCode = some weights ∧
          decodeInt thresholdCode = some threshold ∧
          decodeBoolList membershipCode = some membership ∧
          weights.length = n ∧
          membership.length = n ∧
          List.Forall₂
            (fun weight bit => bit = false → weight = 0)
            weights membership := by
  rw [show decodeSupportedNormalizedGate =
      supportedGateCodec.decode by rfl]
  rw [supportedGateCodec.decode_isSome_iff_exists_encode]
  constructor
  · rintro ⟨gate, hcode⟩
    let weights := List.ofFn gate.gate.weight
    let membership :=
      List.ofFn fun index : Fin n => decide (index ∈ gate.support)
    refine
      ⟨encodeIntList weights, encodeInt gate.gate.threshold,
        encodeBoolList membership, weights, gate.gate.threshold, membership,
        ?_, decodeIntList_encode weights, decodeInt_encode gate.gate.threshold,
        decodeBoolList_encode membership, by simp [weights],
        by simp [membership], ?_⟩
    · rw [← hcode]
      change
        decodeTaggedList
            (encodeTaggedList
              [encodeIntList weights, encodeInt gate.gate.threshold,
                encodeBoolList membership]) =
          some
            [encodeIntList weights, encodeInt gate.gate.threshold,
              encodeBoolList membership]
      exact decodeTaggedList_encode _
    · apply List.forall₂_of_length_eq_of_get
      · simp [weights, membership]
      · intro index hweights hmembership
        simp only [weights, membership, List.get_ofFn]
        intro hfalse
        apply gate.zeroOutside
        simpa using hfalse
  · rintro ⟨weightsCode, thresholdCode, membershipCode, weights, threshold,
      membership, htuple, hweights, hthreshold, hmembership,
      hweightsLength, hmembershipLength, hzeroOutside⟩
    have hzero :
        ∀ index : Fin n,
          listFunction membership hmembershipLength index = false →
            listFunction weights hweightsLength index = 0 := by
      intro index hfalse
      have hpoint :=
        hzeroOutside.get (i := index.val) (by omega) (by omega)
      exact hpoint hfalse
    let gate :=
      supportedGateFromLists n weights threshold membership
        hweightsLength hmembershipLength hzero
    refine ⟨gate, ?_⟩
    change encodeSupportedNormalizedGate gate = raw
    rw [show encodeSupportedNormalizedGate gate =
        encodeTaggedList
          [encodeIntList weights, encodeInt threshold,
            encodeBoolList membership] by
      exact encode_supportedGateFromLists n weights threshold membership
        hweightsLength hmembershipLength hzero]
    rw [encodeIntList_of_decode hweights, encodeInt_of_decode hthreshold,
      encodeBoolList_of_decode hmembership]
    exact encodeTaggedList_of_decode htuple

private def decodeCircuitList
    {Circuit : CircuitFamily}
    (decodeCircuit : (n code : ℕ) → Option (Circuit n))
    (n : ℕ) : List ℕ → Option (List (Circuit n))
  | [] => some []
  | code :: codes => do
      let circuit ← decodeCircuit n code
      let circuits ← decodeCircuitList decodeCircuit n codes
      pure (circuit :: circuits)

private theorem decodeCircuitList_encode
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    {n : ℕ} (circuits : List (Circuit n)) :
    decodeCircuitList codec.decode n (circuits.map codec.encode) =
      some circuits := by
  induction circuits with
  | nil => rfl
  | cons circuit circuits ih =>
      simp [decodeCircuitList, codec.decode_encode, ih]

private theorem decodeCircuitList_isSome_iff
    {Circuit : CircuitFamily}
    (decodeCircuit : (n code : ℕ) → Option (Circuit n))
    (n : ℕ) (codes : List ℕ) :
    (decodeCircuitList decodeCircuit n codes).isSome ↔
      ∀ code, code ∈ codes →
        (decodeCircuit n code).isSome := by
  induction codes with
  | nil =>
      simp [decodeCircuitList]
  | cons code codes inductionHypothesis =>
      cases hdecode : decodeCircuit n code with
      | none =>
          simp [decodeCircuitList, hdecode]
      | some circuit =>
          cases htail :
              decodeCircuitList decodeCircuit n codes with
          | none =>
              have hnot :
                  ¬∀ next, next ∈ codes →
                    (decodeCircuit n next).isSome := by
                intro hall
                have hsome := inductionHypothesis.mpr hall
                simp [htail] at hsome
              simp [decodeCircuitList, hdecode, htail, hnot]
          | some circuits =>
              have hall :
                  ∀ next, next ∈ codes →
                    (decodeCircuit n next).isSome :=
                inductionHypothesis.mp (by simp [htail])
              simpa [decodeCircuitList, hdecode, htail] using hall

private theorem decodeCircuitList_length
    {Circuit : CircuitFamily}
    (decodeCircuit : (n code : ℕ) → Option (Circuit n))
    {n : ℕ} {codes : List ℕ} {circuits : List (Circuit n)}
    (hdecode :
      decodeCircuitList decodeCircuit n codes = some circuits) :
    circuits.length = codes.length := by
  induction codes generalizing circuits with
  | nil =>
      simp [decodeCircuitList] at hdecode
      subst circuits
      rfl
  | cons code codes inductionHypothesis =>
      simp only [decodeCircuitList] at hdecode
      cases hhead : decodeCircuit n code with
      | none =>
          simp [hhead] at hdecode
      | some circuit =>
          have hdecode' :
              (decodeCircuitList decodeCircuit n codes).bind
                  (fun tail => some (circuit :: tail)) =
                some circuits := by
            rw [hhead] at hdecode
            change
              (decodeCircuitList decodeCircuit n codes).bind
                  (fun tail => some (circuit :: tail)) =
                some circuits at hdecode
            exact hdecode
          obtain ⟨tail, htail, hresult⟩ :=
            Option.bind_eq_some_iff.mp hdecode'
          have hcircuits : circuit :: tail = circuits :=
            Option.some.inj hresult
          subst circuits
          simp [inductionHypothesis htail]

private theorem encodeCircuitList_of_decode
    {Circuit : CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    {n : ℕ} {codes : List ℕ} {circuits : List (Circuit n)}
    (hdecode :
      decodeCircuitList codec.decode n codes = some circuits) :
    circuits.map codec.encode = codes := by
  induction codes generalizing circuits with
  | nil =>
      simp [decodeCircuitList] at hdecode
      subst circuits
      rfl
  | cons code codes inductionHypothesis =>
      simp only [decodeCircuitList] at hdecode
      cases hhead : codec.decode n code with
      | none =>
          simp [hhead] at hdecode
      | some circuit =>
          have hdecode' :
              (decodeCircuitList codec.decode n codes).bind
                  (fun tail => some (circuit :: tail)) =
                some circuits := by
            rw [hhead] at hdecode
            change
              (decodeCircuitList codec.decode n codes).bind
                  (fun tail => some (circuit :: tail)) =
                some circuits at hdecode
            exact hdecode
          obtain ⟨tail, htail, hresult⟩ :=
            Option.bind_eq_some_iff.mp hdecode'
          have hcircuits : circuit :: tail = circuits :=
            Option.some.inj hresult
          subst circuits
          simp [codec.encode_decode hhead,
            inductionHypothesis htail]

private def symmetricCircuitFromLists {n : ℕ} (bottomCount : ℕ)
    (bottom : List (SupportedNormalizedGate n)) (top : List Bool)
    (hbottom : bottom.length = bottomCount)
    (htop : top.length = bottomCount + 1) :
    NormalizedSymmetricThresholdCircuit n where
  bottomCount := bottomCount
  bottom := listFunction bottom hbottom
  top := listFunction top htop

private theorem symmetricCircuitFromCanonicalLists
  {n : ℕ} (circuit : NormalizedSymmetricThresholdCircuit n) :
    symmetricCircuitFromLists circuit.bottomCount
      (List.ofFn circuit.bottom) (List.ofFn circuit.top)
      (by simp) (by simp) =
      circuit := by
  cases circuit with
  | mk bottomCount bottom top =>
      simp only [symmetricCircuitFromLists,
        NormalizedSymmetricThresholdCircuit.mk.injEq]
      exact ⟨True.intro, heq_of_eq (listFunction_ofFn _),
        heq_of_eq (listFunction_ofFn _)⟩

private def decodeNormalizedSymmetricThresholdCircuitCandidate
    (n code : ℕ) : Option (NormalizedSymmetricThresholdCircuit n) :=
  match decodeTaggedList code with
  | some [familyTagCode, bottomCountCode, bottomCodesCode, topCode] =>
      match decodeNat familyTagCode, decodeNat bottomCountCode,
          decodeBalancedList bottomCodesCode, decodeBoolList topCode with
      | some familyTag, some bottomCount, some bottomCodes, some top =>
          if familyTag = symmetricCircuitFamilyTag then
            match decodeCircuitList decodeSupportedNormalizedGate n
                bottomCodes with
            | some bottom =>
                if hbottom : bottom.length = bottomCount then
                  if htop : top.length = bottomCount + 1 then
                    some (symmetricCircuitFromLists bottomCount bottom top
                      hbottom htop)
                  else none
                else none
            | none => none
          else none
      | _, _, _, _ => none
  | _ => none

/-- Canonical decoder for normalized `SYM ∘ THR` syntax. -/
def decodeNormalizedSymmetricThresholdCircuit
    (n code : ℕ) : Option (NormalizedSymmetricThresholdCircuit n) :=
  (decodeNormalizedSymmetricThresholdCircuitCandidate n code).bind
    fun circuit =>
      if encodeNormalizedSymmetricThresholdCircuit circuit = code then
        some circuit
      else none

theorem encodeNormalizedSymmetricThresholdCircuit_of_decode
    {n code : ℕ} {circuit : NormalizedSymmetricThresholdCircuit n}
    (hdecode : decodeNormalizedSymmetricThresholdCircuit n code =
      some circuit) :
    encodeNormalizedSymmetricThresholdCircuit circuit = code := by
  unfold decodeNormalizedSymmetricThresholdCircuit at hdecode
  generalize hcandidate :
    decodeNormalizedSymmetricThresholdCircuitCandidate n code =
      candidate at hdecode
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

theorem decodeNormalizedSymmetricThresholdCircuit_encode
    {n : ℕ} (circuit : NormalizedSymmetricThresholdCircuit n) :
    decodeNormalizedSymmetricThresholdCircuit n
      (encodeNormalizedSymmetricThresholdCircuit circuit) =
        some circuit := by
  unfold decodeNormalizedSymmetricThresholdCircuit
  unfold decodeNormalizedSymmetricThresholdCircuitCandidate
  unfold encodeNormalizedSymmetricThresholdCircuit
  rw [decodeTaggedList_encode]
  dsimp only
  rw [decodeNat_encode, decodeNat_encode, decodeBalancedList_encode,
    decodeBoolList_encode]
  simp only [if_pos]
  have hdecode :
      decodeCircuitList decodeSupportedNormalizedGate n
          ((List.ofFn circuit.bottom).map
            encodeSupportedNormalizedGate) =
        some (List.ofFn circuit.bottom) := by
    simpa [supportedGateCodec] using
      (decodeCircuitList_encode supportedGateCodec
        (List.ofFn circuit.bottom))
  have hcodes :
      (List.ofFn fun index =>
        encodeSupportedNormalizedGate (circuit.bottom index)) =
        (List.ofFn circuit.bottom).map
          encodeSupportedNormalizedGate := by
    apply List.ext_get
    · simp
    · intro index hleft hright
      simp
  rw [hcodes]
  rw [hdecode]
  simp only [List.length_ofFn]
  simp only [dif_pos True.intro, Option.bind_some]
  rw [symmetricCircuitFromCanonicalLists]
  simp [Function.comp_def]

/-- Exact field-level contract consumed by the executable symmetric-circuit
validator.  It exposes only canonical component decoders and length checks. -/
def SymmetricThresholdCircuitFieldsValid (n code : ℕ) : Prop :=
  ∃ familyTagCode bottomCountCode bottomCodesCode topCode
      bottomCount bottomCodes top,
    decodeTaggedList code =
        some [familyTagCode, bottomCountCode, bottomCodesCode, topCode] ∧
      decodeNat familyTagCode = some symmetricCircuitFamilyTag ∧
      decodeNat bottomCountCode = some bottomCount ∧
      decodeBalancedList bottomCodesCode = some bottomCodes ∧
      (∀ bottomCode, bottomCode ∈ bottomCodes →
        (decodeSupportedNormalizedGate n bottomCode).isSome) ∧
      decodeBoolList topCode = some top ∧
      bottomCodes.length = bottomCount ∧
      top.length = bottomCount + 1

theorem decodeNormalizedSymmetricThresholdCircuit_isSome_iff_fields
    (n code : ℕ) :
    (decodeNormalizedSymmetricThresholdCircuit n code).isSome ↔
      SymmetricThresholdCircuitFieldsValid n code := by
  constructor
  · intro hsome
    obtain ⟨circuit, hdecode⟩ :=
      Option.isSome_iff_exists.mp hsome
    have hencode :=
      encodeNormalizedSymmetricThresholdCircuit_of_decode hdecode
    let bottom := List.ofFn circuit.bottom
    let bottomCodes := bottom.map encodeSupportedNormalizedGate
    let top := List.ofFn circuit.top
    refine
      ⟨encodeNat symmetricCircuitFamilyTag,
        encodeNat circuit.bottomCount,
        encodeBalancedList bottomCodes, encodeBoolList top,
        circuit.bottomCount, bottomCodes, top, ?_, by simp, by simp,
        by simp, ?_, by simp, by simp [bottomCodes, bottom],
        by simp [top]⟩
    · rw [← hencode]
      simp [encodeNormalizedSymmetricThresholdCircuit, bottomCodes,
        bottom, top, Function.comp_def]
    · intro bottomCode hmember
      obtain ⟨gate, _, rfl⟩ := List.mem_map.mp hmember
      simp [decodeSupportedNormalizedGate_encode]
  · rintro ⟨familyTagCode, bottomCountCode, bottomCodesCode, topCode,
      bottomCount, bottomCodes, top, htuple, hfamily, hcount,
      hbottomCodes, hall, htop, hbottomLength, htopLength⟩
    have hbottomSome :
        (decodeCircuitList decodeSupportedNormalizedGate
          n bottomCodes).isSome :=
      (decodeCircuitList_isSome_iff
        decodeSupportedNormalizedGate n bottomCodes).2 hall
    obtain ⟨bottom, hbottomDecode⟩ :=
      Option.isSome_iff_exists.mp hbottomSome
    have hdecodedLength : bottom.length = bottomCodes.length :=
      decodeCircuitList_length decodeSupportedNormalizedGate
        hbottomDecode
    have hbottomLength' : bottom.length = bottomCount := by
      omega
    let circuit :=
      symmetricCircuitFromLists bottomCount bottom top
        hbottomLength' htopLength
    have hbottomEncode :
        bottom.map encodeSupportedNormalizedGate = bottomCodes := by
      simpa [supportedGateCodec] using
        (encodeCircuitList_of_decode supportedGateCodec hbottomDecode)
    have hbottomCanonical :
        (List.ofFn fun index =>
          encodeSupportedNormalizedGate
            (listFunction bottom hbottomLength' index)) =
          bottom.map encodeSupportedNormalizedGate := by
      calc
        _ = (List.ofFn (listFunction bottom hbottomLength')).map
              encodeSupportedNormalizedGate := by
                apply List.ext_get
                · simp
                · intro index hleft hright
                  simp
        _ = _ := by rw [ofFn_listFunction]
    have htopCanonical :
        List.ofFn (listFunction top htopLength) = top :=
      ofFn_listFunction top htopLength
    have hcanonical :
        encodeNormalizedSymmetricThresholdCircuit circuit = code := by
      calc
        encodeNormalizedSymmetricThresholdCircuit circuit =
            encodeTaggedList
              [encodeNat symmetricCircuitFamilyTag,
                encodeNat bottomCount,
                encodeBalancedList
                  (bottom.map encodeSupportedNormalizedGate),
                encodeBoolList top] := by
                  rw [encodeNormalizedSymmetricThresholdCircuit]
                  change
                    encodeTaggedList
                      [encodeNat symmetricCircuitFamilyTag,
                        encodeNat bottomCount,
                        encodeBalancedList
                          (List.ofFn fun index =>
                            encodeSupportedNormalizedGate
                              (listFunction bottom hbottomLength'
                                index)),
                        encodeBoolList
                          (List.ofFn
                            (listFunction top htopLength))] =
                      _
                  rw [hbottomCanonical, htopCanonical]
        _ = encodeTaggedList
              [familyTagCode, bottomCountCode, bottomCodesCode,
                topCode] := by
                  rw [encodeNat_of_decode hfamily,
                    encodeNat_of_decode hcount, hbottomEncode,
                    encodeBalancedList_of_decode hbottomCodes,
                    encodeBoolList_of_decode htop]
        _ = code := encodeTaggedList_of_decode htuple
    rw [← hcanonical]
    exact Option.isSome_iff_exists.mpr
      ⟨circuit,
        decodeNormalizedSymmetricThresholdCircuit_encode circuit⟩

private def thresholdCircuitFromList {n : ℕ} (bottomCount : ℕ)
    (bottom : List (SupportedNormalizedGate n))
    (hbottom : bottom.length = bottomCount)
    (top : SupportedNormalizedGate bottomCount) :
    NormalizedThresholdThresholdCircuit n where
  bottomCount := bottomCount
  bottom := listFunction bottom hbottom
  top := top

private theorem thresholdCircuitFromCanonicalList
    {n : ℕ} (circuit : NormalizedThresholdThresholdCircuit n) :
    thresholdCircuitFromList circuit.bottomCount
      (List.ofFn circuit.bottom) (by simp) circuit.top = circuit := by
  cases circuit with
  | mk bottomCount bottom top =>
      simp only [thresholdCircuitFromList,
        NormalizedThresholdThresholdCircuit.mk.injEq]
      exact ⟨True.intro, heq_of_eq (listFunction_ofFn _), HEq.rfl⟩

private def decodeNormalizedThresholdThresholdCircuitCandidate
    (n code : ℕ) : Option (NormalizedThresholdThresholdCircuit n) :=
  match decodeTaggedList code with
  | some [familyTagCode, bottomCountCode, bottomCodesCode, topCode] =>
      match decodeNat familyTagCode, decodeNat bottomCountCode,
          decodeBalancedList bottomCodesCode with
      | some familyTag, some bottomCount, some bottomCodes =>
          if familyTag = thresholdCircuitFamilyTag then
            match decodeCircuitList decodeSupportedNormalizedGate n
                bottomCodes with
            | some bottom =>
                if hbottom : bottom.length = bottomCount then
                  match decodeSupportedNormalizedGate bottomCount topCode with
                  | some top =>
                      some (thresholdCircuitFromList bottomCount bottom
                        hbottom top)
                  | none => none
                else none
            | none => none
          else none
      | _, _, _ => none
  | _ => none

/-- Canonical decoder for normalized `THR ∘ THR` syntax. -/
def decodeNormalizedThresholdThresholdCircuit
    (n code : ℕ) : Option (NormalizedThresholdThresholdCircuit n) :=
  (decodeNormalizedThresholdThresholdCircuitCandidate n code).bind
    fun circuit =>
      if encodeNormalizedThresholdThresholdCircuit circuit = code then
        some circuit
      else none

theorem encodeNormalizedThresholdThresholdCircuit_of_decode
    {n code : ℕ} {circuit : NormalizedThresholdThresholdCircuit n}
    (hdecode : decodeNormalizedThresholdThresholdCircuit n code =
      some circuit) :
    encodeNormalizedThresholdThresholdCircuit circuit = code := by
  unfold decodeNormalizedThresholdThresholdCircuit at hdecode
  generalize hcandidate :
    decodeNormalizedThresholdThresholdCircuitCandidate n code =
      candidate at hdecode
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

theorem decodeNormalizedThresholdThresholdCircuit_encode
    {n : ℕ} (circuit : NormalizedThresholdThresholdCircuit n) :
    decodeNormalizedThresholdThresholdCircuit n
      (encodeNormalizedThresholdThresholdCircuit circuit) =
        some circuit := by
  unfold decodeNormalizedThresholdThresholdCircuit
  unfold decodeNormalizedThresholdThresholdCircuitCandidate
  unfold encodeNormalizedThresholdThresholdCircuit
  rw [decodeTaggedList_encode]
  dsimp only
  rw [decodeNat_encode, decodeNat_encode, decodeBalancedList_encode]
  simp only [if_pos]
  have hbottomDecode :
      decodeCircuitList decodeSupportedNormalizedGate n
          ((List.ofFn circuit.bottom).map
            encodeSupportedNormalizedGate) =
        some (List.ofFn circuit.bottom) := by
    simpa [supportedGateCodec] using
      (decodeCircuitList_encode supportedGateCodec
        (List.ofFn circuit.bottom))
  rw [show
    (List.ofFn fun index =>
      encodeSupportedNormalizedGate (circuit.bottom index)) =
        (List.ofFn circuit.bottom).map
          encodeSupportedNormalizedGate by
            apply List.ext_get
            · simp
            · intro index hleft hright
              simp]
  rw [hbottomDecode]
  simp only [List.length_ofFn, dif_pos True.intro]
  rw [decodeSupportedNormalizedGate_encode circuit.top]
  simp only [Option.bind_some]
  rw [thresholdCircuitFromCanonicalList]
  simp [Function.comp_def]

/-- Exact field-level contract consumed by the executable threshold-circuit
validator. -/
def ThresholdThresholdCircuitFieldsValid (n code : ℕ) : Prop :=
  ∃ familyTagCode bottomCountCode bottomCodesCode topCode
      bottomCount bottomCodes,
    decodeTaggedList code =
        some [familyTagCode, bottomCountCode, bottomCodesCode, topCode] ∧
      decodeNat familyTagCode = some thresholdCircuitFamilyTag ∧
      decodeNat bottomCountCode = some bottomCount ∧
      decodeBalancedList bottomCodesCode = some bottomCodes ∧
      (∀ bottomCode, bottomCode ∈ bottomCodes →
        (decodeSupportedNormalizedGate n bottomCode).isSome) ∧
      (decodeSupportedNormalizedGate bottomCount topCode).isSome ∧
      bottomCodes.length = bottomCount

theorem decodeNormalizedThresholdThresholdCircuit_isSome_iff_fields
    (n code : ℕ) :
    (decodeNormalizedThresholdThresholdCircuit n code).isSome ↔
      ThresholdThresholdCircuitFieldsValid n code := by
  constructor
  · intro hsome
    obtain ⟨circuit, hdecode⟩ :=
      Option.isSome_iff_exists.mp hsome
    have hencode :=
      encodeNormalizedThresholdThresholdCircuit_of_decode hdecode
    let bottom := List.ofFn circuit.bottom
    let bottomCodes := bottom.map encodeSupportedNormalizedGate
    refine
      ⟨encodeNat thresholdCircuitFamilyTag,
        encodeNat circuit.bottomCount,
        encodeBalancedList bottomCodes,
        encodeSupportedNormalizedGate circuit.top,
        circuit.bottomCount, bottomCodes, ?_, by simp, by simp,
        by simp, ?_,
        by
          rw [decodeSupportedNormalizedGate_encode]
          rfl,
        by simp [bottomCodes, bottom]⟩
    · rw [← hencode]
      simp [encodeNormalizedThresholdThresholdCircuit, bottomCodes,
        bottom, Function.comp_def]
    · intro bottomCode hmember
      obtain ⟨gate, _, rfl⟩ := List.mem_map.mp hmember
      simp [decodeSupportedNormalizedGate_encode]
  · rintro ⟨familyTagCode, bottomCountCode, bottomCodesCode, topCode,
      bottomCount, bottomCodes, htuple, hfamily, hcount,
      hbottomCodes, hall, htopSome, hbottomLength⟩
    have hbottomSome :
        (decodeCircuitList decodeSupportedNormalizedGate
          n bottomCodes).isSome :=
      (decodeCircuitList_isSome_iff
        decodeSupportedNormalizedGate n bottomCodes).2 hall
    obtain ⟨bottom, hbottomDecode⟩ :=
      Option.isSome_iff_exists.mp hbottomSome
    obtain ⟨top, htopDecode⟩ :=
      Option.isSome_iff_exists.mp htopSome
    have hdecodedLength : bottom.length = bottomCodes.length :=
      decodeCircuitList_length decodeSupportedNormalizedGate
        hbottomDecode
    have hbottomLength' : bottom.length = bottomCount := by
      omega
    let circuit :=
      thresholdCircuitFromList bottomCount bottom hbottomLength' top
    have hbottomEncode :
        bottom.map encodeSupportedNormalizedGate = bottomCodes := by
      simpa [supportedGateCodec] using
        (encodeCircuitList_of_decode supportedGateCodec hbottomDecode)
    have htopEncode :
        encodeSupportedNormalizedGate top = topCode :=
      encodeSupportedNormalizedGate_of_decode htopDecode
    have hbottomCanonical :
        (List.ofFn fun index =>
          encodeSupportedNormalizedGate
            (listFunction bottom hbottomLength' index)) =
          bottom.map encodeSupportedNormalizedGate := by
      calc
        _ = (List.ofFn (listFunction bottom hbottomLength')).map
              encodeSupportedNormalizedGate := by
                apply List.ext_get
                · simp
                · intro index hleft hright
                  simp
        _ = _ := by rw [ofFn_listFunction]
    have hcanonical :
        encodeNormalizedThresholdThresholdCircuit circuit = code := by
      calc
        encodeNormalizedThresholdThresholdCircuit circuit =
            encodeTaggedList
              [encodeNat thresholdCircuitFamilyTag,
                encodeNat bottomCount,
                encodeBalancedList
                  (bottom.map encodeSupportedNormalizedGate),
                encodeSupportedNormalizedGate top] := by
                  rw [encodeNormalizedThresholdThresholdCircuit]
                  change
                    encodeTaggedList
                      [encodeNat thresholdCircuitFamilyTag,
                        encodeNat bottomCount,
                        encodeBalancedList
                          (List.ofFn fun index =>
                            encodeSupportedNormalizedGate
                              (listFunction bottom hbottomLength'
                                index)),
                        encodeSupportedNormalizedGate top] =
                      _
                  rw [hbottomCanonical]
        _ = encodeTaggedList
              [familyTagCode, bottomCountCode, bottomCodesCode,
                topCode] := by
                  rw [encodeNat_of_decode hfamily,
                    encodeNat_of_decode hcount, hbottomEncode,
                    encodeBalancedList_of_decode hbottomCodes,
                    htopEncode]
        _ = code := encodeTaggedList_of_decode htuple
    rw [← hcanonical]
    exact Option.isSome_iff_exists.mpr
      ⟨circuit,
        decodeNormalizedThresholdThresholdCircuit_encode circuit⟩

/-- Reusable canonical codec for the normalized `SYM ∘ THR` family. -/
def symmetricCircuitCodec :
    CanonicalCircuitCodec NormalizedSymmetricThresholdCircuit where
  encode := encodeNormalizedSymmetricThresholdCircuit
  decode := decodeNormalizedSymmetricThresholdCircuit
  decode_encode := decodeNormalizedSymmetricThresholdCircuit_encode
  encode_decode := by
    intro n code circuit hdecode
    exact encodeNormalizedSymmetricThresholdCircuit_of_decode hdecode

/-- Reusable canonical codec for the normalized `THR ∘ THR` family. -/
def thresholdCircuitCodec :
    CanonicalCircuitCodec NormalizedThresholdThresholdCircuit where
  encode := encodeNormalizedThresholdThresholdCircuit
  decode := decodeNormalizedThresholdThresholdCircuit
  decode_encode := decodeNormalizedThresholdThresholdCircuit_encode
  encode_decode := by
    intro n code circuit hdecode
    exact encodeNormalizedThresholdThresholdCircuit_of_decode hdecode

/-! ## Canonical Boolean DAGs -/

private def decodeBooleanNodeCandidate
    (n code : ℕ) : Option (BooleanNode n) :=
  match decodeTaggedList code with
  | some [tagCode, payloadCode] =>
      match decodeNat tagCode, decodeNat payloadCode with
      | some 0, some payload =>
          if payload = 0 then some (.const false)
          else if payload = 1 then some (.const true)
          else none
      | some 1, some payload =>
          if hindex : payload < n then some (.input ⟨payload, hindex⟩)
          else none
      | some 2, some child => some (.not child)
      | _, _ => none
  | some [tagCode, leftCode, rightCode] =>
      match decodeNat tagCode, decodeNat leftCode, decodeNat rightCode with
      | some 3, some left, some right => some (.and left right)
      | some 4, some left, some right => some (.or left right)
      | _, _, _ => none
  | _ => none

/-- Partial decoder for one Boolean DAG node. -/
def decodeBooleanNode (n code : ℕ) : Option (BooleanNode n) :=
  (decodeBooleanNodeCandidate n code).bind fun node =>
    if encodeBooleanNode node = code then some node else none

theorem decodeBooleanNode_encode
    {n : ℕ} (node : BooleanNode n) :
    decodeBooleanNode n (encodeBooleanNode node) = some node := by
  cases node with
  | const value =>
      cases value <;>
        simp [decodeBooleanNode, decodeBooleanNodeCandidate,
          encodeBooleanNode]
  | input index =>
      unfold decodeBooleanNode decodeBooleanNodeCandidate encodeBooleanNode
      rw [decodeTaggedList_encode]
      dsimp only
      rw [decodeNat_encode, decodeNat_encode]
      change
        ((if hindex : index.val < n then
            some (BooleanNode.input ⟨index.val, hindex⟩)
          else none).bind fun decoded =>
            if encodeBooleanNode decoded =
                encodeBooleanNode (BooleanNode.input index) then
              some decoded
            else none) =
          some (BooleanNode.input index)
      rw [dif_pos index.isLt]
      simp
  | not child =>
      unfold decodeBooleanNode decodeBooleanNodeCandidate encodeBooleanNode
      rw [decodeTaggedList_encode]
      dsimp only
      rw [decodeNat_encode, decodeNat_encode]
      simp
  | and left right =>
      unfold decodeBooleanNode decodeBooleanNodeCandidate encodeBooleanNode
      rw [decodeTaggedList_encode]
      dsimp only
      rw [decodeNat_encode, decodeNat_encode, decodeNat_encode]
      simp
  | or left right =>
      unfold decodeBooleanNode decodeBooleanNodeCandidate encodeBooleanNode
      rw [decodeTaggedList_encode]
      dsimp only
      rw [decodeNat_encode, decodeNat_encode, decodeNat_encode]
      simp

private def decodeBooleanNodes
    (n : ℕ) : List ℕ → Option (List (BooleanNode n))
  | [] => some []
  | code :: codes => do
      let node ← decodeBooleanNode n code
      let nodes ← decodeBooleanNodes n codes
      pure (node :: nodes)

private theorem decodeBooleanNodes_encode
    {n : ℕ} (nodes : List (BooleanNode n)) :
    decodeBooleanNodes n (nodes.map encodeBooleanNode) = some nodes := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      simp [decodeBooleanNodes, decodeBooleanNode_encode, ih]

private def booleanCircuitFromNodes {n : ℕ}
    (nodes : List (BooleanNode n)) (output : ℕ)
    (houtput : output < nodes.length)
    (hwellFormed : ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val) :
    BooleanCircuit n where
  nodes := nodes
  output := ⟨output, houtput⟩
  wellFormed := hwellFormed

instance BooleanNode.decidableWellFormedAt
    {n index : ℕ} (node : BooleanNode n) :
    Decidable (node.WellFormedAt index) := by
  cases node with
  | const _ => exact isTrue True.intro
  | input _ => exact isTrue True.intro
  | not child =>
      change Decidable (child < index)
      exact inferInstance
  | and left right =>
      change Decidable (left < index ∧ right < index)
      exact inferInstance
  | or left right =>
      change Decidable (left < index ∧ right < index)
      exact inferInstance

private def decodeBooleanCircuitCandidate
    (n code : ℕ) : Option (BooleanCircuit n) :=
  match decodeTaggedList code with
  | some [nodesCode, outputCode] =>
      match decodeBalancedList nodesCode, decodeNat outputCode with
      | some nodeCodes, some output =>
          match decodeBooleanNodes n nodeCodes with
          | some nodes =>
              if houtput : output < nodes.length then
                if hwellFormed : ∀ index : Fin nodes.length,
                    (nodes.get index).WellFormedAt index.val then
                  some (booleanCircuitFromNodes nodes output
                    houtput hwellFormed)
                else none
              else none
          | none => none
      | _, _ => none
  | _ => none

/-- Canonical decoder for a topologically well-formed Boolean DAG. -/
def decodeBooleanCircuit
    (n code : ℕ) : Option (BooleanCircuit n) :=
  (decodeBooleanCircuitCandidate n code).bind fun circuit =>
    if encodeBooleanCircuit circuit = code then some circuit else none

@[simp] theorem decodeBooleanCircuit_zero (n : ℕ) :
    decodeBooleanCircuit n 0 = none := by
  rfl

theorem encodeBooleanCircuit_of_decode
    {n code : ℕ} {circuit : BooleanCircuit n}
    (hdecode : decodeBooleanCircuit n code = some circuit) :
    encodeBooleanCircuit circuit = code := by
  unfold decodeBooleanCircuit at hdecode
  generalize hcandidate :
    decodeBooleanCircuitCandidate n code = candidate at hdecode
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

private theorem booleanCircuitFromCanonicalNodes
    {n : ℕ} (circuit : BooleanCircuit n) :
    booleanCircuitFromNodes circuit.nodes circuit.output.val
      circuit.output.isLt circuit.wellFormed = circuit := by
  cases circuit
  rfl

theorem decodeBooleanCircuit_encode
    {n : ℕ} (circuit : BooleanCircuit n) :
    decodeBooleanCircuit n (encodeBooleanCircuit circuit) =
      some circuit := by
  unfold decodeBooleanCircuit decodeBooleanCircuitCandidate
  unfold encodeBooleanCircuit
  rw [decodeTaggedList_encode]
  dsimp only
  rw [decodeBalancedList_encode, decodeNat_encode]
  dsimp only
  rw [decodeBooleanNodes_encode circuit.nodes]
  dsimp only
  rw [dif_pos circuit.output.isLt, dif_pos circuit.wellFormed]
  simp only [Option.bind_some]
  rw [booleanCircuitFromCanonicalNodes]
  simp

/-! ## Checked fourfold requests -/

/-! ## Canonical rational coefficients and legal sums -/

/-- Reduced `Rat.num`/`Rat.den` is the unique coefficient syntax. -/
def encodeCanonicalRational (coefficient : ℚ) : ℕ :=
  encodeTaggedList
    [encodeInt coefficient.num, encodeNat coefficient.den]

private def decodeCanonicalRationalCandidate (code : ℕ) : Option ℚ :=
  match decodeTaggedList code with
  | some [numeratorCode, denominatorCode] =>
      match decodeInt numeratorCode, decodeNat denominatorCode with
      | some numerator, some denominator =>
          if hdenominator : denominator ≠ 0 then
            some (Rat.normalize numerator denominator hdenominator)
          else none
      | _, _ => none
  | _ => none

/-- Partial canonical rational decoder; unreduced and alternate integer codes
are rejected by exact re-encoding. -/
def decodeCanonicalRational (code : ℕ) : Option ℚ :=
  (decodeCanonicalRationalCandidate code).bind fun coefficient =>
    if encodeCanonicalRational coefficient = code then
      some coefficient
    else none

theorem encodeCanonicalRational_of_decode
    {code : ℕ} {coefficient : ℚ}
    (hdecode : decodeCanonicalRational code = some coefficient) :
    encodeCanonicalRational coefficient = code := by
  unfold decodeCanonicalRational at hdecode
  generalize hcandidate :
    decodeCanonicalRationalCandidate code = candidate at hdecode
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

theorem decodeCanonicalRational_encode (coefficient : ℚ) :
    decodeCanonicalRational (encodeCanonicalRational coefficient) =
      some coefficient := by
  unfold decodeCanonicalRational decodeCanonicalRationalCandidate
  unfold encodeCanonicalRational
  rw [decodeTaggedList_encode]
  dsimp only
  rw [decodeInt_encode, decodeNat_encode]
  dsimp only
  rw [dif_pos coefficient.den_nz]
  simp [Rat.normalize_self]

structure LegalCircuitTerm (Circuit : CircuitFamily) (n : ℕ) where
  coefficient : ℚ
  circuit : Circuit n

def LegalCircuitTerm.code
    {Circuit : CircuitFamily} {n : ℕ}
    (codec : CanonicalCircuitCodec Circuit)
    (term : LegalCircuitTerm Circuit n) : ℕ :=
  encodeTaggedList
    [encodeCanonicalRational term.coefficient,
      codec.encode term.circuit]

private def decodeLegalCircuitTermCandidate
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (n code : ℕ) : Option (LegalCircuitTerm Circuit n) := do
  let fields ← decodeTaggedList code
  match fields with
  | [coefficientCode, circuitCode] =>
      let coefficient ← decodeCanonicalRational coefficientCode
      let circuit ← codec.decode n circuitCode
      pure ⟨coefficient, circuit⟩
  | _ => none

private def decodeLegalCircuitTerm
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (n code : ℕ) : Option (LegalCircuitTerm Circuit n) :=
  (decodeLegalCircuitTermCandidate codec n code).bind fun term =>
    if term.code codec = code then some term else none

set_option maxHeartbeats 1000000 in
-- Dependent circuit fields make normalization of the canonical term proof costly.
theorem decodeLegalCircuitTerm_encode
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    {n : ℕ} (term : LegalCircuitTerm Circuit n) :
    decodeLegalCircuitTerm codec n (term.code codec) = some term := by
  have hcandidate :
      decodeLegalCircuitTermCandidate codec n (term.code codec) =
        some term := by
    cases term with
    | mk coefficient circuit =>
        unfold decodeLegalCircuitTermCandidate LegalCircuitTerm.code
        rw [decodeTaggedList_encode]
        change
          (do
            let decodedCoefficient ←
              decodeCanonicalRational
                (encodeCanonicalRational coefficient)
            let decodedCircuit ← codec.decode n (codec.encode circuit)
            pure
              ({ coefficient := decodedCoefficient
                 circuit := decodedCircuit } :
                LegalCircuitTerm Circuit n)) =
            some
              ({ coefficient := coefficient
                 circuit := circuit } :
                LegalCircuitTerm Circuit n)
        rw [decodeCanonicalRational_encode, codec.decode_encode]
        rfl
  unfold decodeLegalCircuitTerm
  rw [hcandidate]
  simp

private def decodeLegalCircuitTerms
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (n : ℕ) : List ℕ → Option (List (LegalCircuitTerm Circuit n))
  | [] => some []
  | code :: codes => do
      let term ← decodeLegalCircuitTerm codec n code
      let terms ← decodeLegalCircuitTerms codec n codes
      pure (term :: terms)

private theorem decodeLegalCircuitTerms_encode
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    {n : ℕ} (terms : List (LegalCircuitTerm Circuit n)) :
    decodeLegalCircuitTerms codec n (terms.map (·.code codec)) =
      some terms := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp [decodeLegalCircuitTerms, decodeLegalCircuitTerm_encode, ih]

/-- Typed syntax for one rational linear combination of normalized atoms. -/
structure LegalCircuitSumDescription (Circuit : CircuitFamily) where
  q : ℕ
  terms : List (LegalCircuitTerm Circuit q)

def LegalCircuitSumDescription.code
    {Circuit : CircuitFamily} (codec : CanonicalCircuitCodec Circuit)
    (description : LegalCircuitSumDescription Circuit) : ℕ :=
  encodeTaggedList
    [encodeNat description.q,
      encodeBalancedList (description.terms.map (·.code codec))]

def LegalCircuitSumDescription.coefficientMass
    {Circuit : CircuitFamily}
    (description : LegalCircuitSumDescription Circuit) : ℚ :=
  description.terms.foldl
    (fun total term => total + |term.coefficient|) 0

structure LegalSumLimits where
  expectedArity : ℕ
  termCap : ℕ
  coefficientBitCap : ℕ
  coefficientMassCap : ℚ
  wireCap : ℕ
  descriptionCap : ℕ

/-- Successful decoding certifies every finite witness envelope. -/
structure CheckedLegalCircuitSum
    (Circuit : CircuitFamily)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits) where
  value : LegalCircuitSumDescription Circuit
  arity_eq : value.q = limits.expectedArity
  terms_le : value.terms.length ≤ limits.termCap
  coefficient_bits_le : ∀ term ∈ value.terms,
    natBitLength term.coefficient.num.natAbs ≤ limits.coefficientBitCap ∧
    natBitLength term.coefficient.den ≤ limits.coefficientBitCap
  mass_le : value.coefficientMass ≤ limits.coefficientMassCap
  wires_le : ∀ term ∈ value.terms,
    wires term.circuit ≤ limits.wireCap
  description_le : ∀ term ∈ value.terms,
    description term.circuit ≤ limits.descriptionCap

def CheckedLegalCircuitSum.code
    {Circuit : CircuitFamily}
    {wires description : {n : ℕ} → Circuit n → ℕ}
    {limits : LegalSumLimits}
    (codec : CanonicalCircuitCodec Circuit)
    (checked : CheckedLegalCircuitSum Circuit wires description limits) : ℕ :=
  checked.value.code codec

private def decodeLegalCircuitSumCandidate
    {Circuit : CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits) (code : ℕ) :
    Option (CheckedLegalCircuitSum Circuit wires description limits) :=
  match decodeTaggedList code with
  | some [qCode, termCodesCode] =>
      match decodeNat qCode, decodeBalancedList termCodesCode with
      | some q, some termCodes =>
          if harity : q = limits.expectedArity then
            match decodeLegalCircuitTerms codec q termCodes with
            | some terms =>
                let value : LegalCircuitSumDescription Circuit := ⟨q, terms⟩
                if hterms : value.terms.length ≤ limits.termCap then
                  if hbits : ∀ term ∈ value.terms,
                      natBitLength term.coefficient.num.natAbs ≤
                          limits.coefficientBitCap ∧
                        natBitLength term.coefficient.den ≤
                          limits.coefficientBitCap then
                    if hmass :
                        value.coefficientMass ≤ limits.coefficientMassCap then
                      if hwires : ∀ term ∈ value.terms,
                          wires term.circuit ≤ limits.wireCap then
                        if hdescription : ∀ term ∈ value.terms,
                            description term.circuit ≤
                              limits.descriptionCap then
                          some
                            { value := value
                              arity_eq := harity
                              terms_le := hterms
                              coefficient_bits_le := hbits
                              mass_le := hmass
                              wires_le := hwires
                              description_le := hdescription }
                        else none
                      else none
                    else none
                  else none
                else none
            | none => none
          else none
      | _, _ => none
  | _ => none

/-- Canonical decode-or-reject boundary for the complete recovery sum. -/
def decodeLegalCircuitSum
    {Circuit : CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits) (code : ℕ) :
    Option (CheckedLegalCircuitSum Circuit wires description limits) :=
  (decodeLegalCircuitSumCandidate codec wires description limits code).bind
    fun checked =>
      if checked.code codec = code then some checked else none

theorem CheckedLegalCircuitSum.code_of_decode
    {Circuit : CircuitFamily}
    {codec : CanonicalCircuitCodec Circuit}
    {wires description : {n : ℕ} → Circuit n → ℕ}
    {limits : LegalSumLimits} {code : ℕ}
    {checked : CheckedLegalCircuitSum Circuit wires description limits}
    (hdecode :
      decodeLegalCircuitSum codec wires description limits code =
        some checked) :
    checked.code codec = code := by
  unfold decodeLegalCircuitSum at hdecode
  generalize hcandidate :
    decodeLegalCircuitSumCandidate codec wires description limits code =
      candidate at hdecode
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

private theorem checkedLegalCircuitSum_ext
    {Circuit : CircuitFamily}
    {wires description : {n : ℕ} → Circuit n → ℕ}
    {limits : LegalSumLimits}
    (left right : CheckedLegalCircuitSum Circuit wires description limits)
    (hvalue : left.value = right.value) :
    left = right := by
  cases left
  cases right
  cases hvalue
  rfl

theorem decodeLegalCircuitSum_encode
    {Circuit : CircuitFamily}
    (codec : CanonicalCircuitCodec Circuit)
    (wires description : {n : ℕ} → Circuit n → ℕ)
    (limits : LegalSumLimits)
    (checked : CheckedLegalCircuitSum Circuit wires description limits) :
    decodeLegalCircuitSum codec wires description limits
      (checked.code codec) = some checked := by
  cases checked with
  | mk value harity hterms hbits hmass hwires hdescription =>
      cases value with
      | mk q terms =>
          unfold decodeLegalCircuitSum
          unfold decodeLegalCircuitSumCandidate
          unfold CheckedLegalCircuitSum.code LegalCircuitSumDescription.code
          rw [decodeTaggedList_encode]
          dsimp only
          rw [decodeNat_encode, decodeBalancedList_encode]
          dsimp only
          rw [dif_pos harity]
          rw [decodeLegalCircuitTerms_encode codec terms]
          dsimp only
          rw [dif_pos hterms, dif_pos hbits, dif_pos hmass,
            dif_pos hwires, dif_pos hdescription]
          simp only [Option.bind_some]
          split
          · apply congrArg some
            apply checkedLegalCircuitSum_ext
            rfl
          · rename_i hnoncanonical
            exact False.elim (hnoncanonical True.intro)

/-! ## One mode-tagged weak-witness boundary -/

/-- Both class branches share one public general-oracle arity and DAG-size
bound.  Arity equalities are part of the fixed verifier configuration, not
data supplied by the witness. -/
structure RecoveryWitnessLimits where
  oracleArity : ℕ
  oracleSizeCap : ℕ
  sumArity : ℕ
  symmetric : LegalSumLimits
  threshold : LegalSumLimits
  symmetricArity : symmetric.expectedArity = sumArity
  thresholdArity : threshold.expectedArity = sumArity

end NearCubicWires.CanonicalWitnessCodec
