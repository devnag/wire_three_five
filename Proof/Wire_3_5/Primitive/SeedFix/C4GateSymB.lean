import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymR
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.SymDataCost

/-! # G2, the SYM gate-frame writer, part 4: the budget and the writer at every call

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050), and the call's
preprocessing is polynomial in `n` (`prim:runtime`, P3:3105-3115). This part fixes the writer's fill count and bounds its
steps at every SYM call of the gate's family:

* `needW`, the fill count's coefficient and degree `CvS`, `DvS` (`needW_le`: `W = CvS·(n+1)^DvS` covers the codes'
  bits and the envelopes, PA's `CallSize`); `sym_call_facts`, `sym_data_hyps` (PA's data stage's hypotheses from
  `I.Call`);
* `pool_bounds`: the pool's size and the slots' widths are at most `6·DC` (the tables are written within the data
  stage's `DC` steps, `one_tape_support`);
* `cost_le`, `pb_costN`: the writer's steps are at most `costN n`, polynomially bounded (`gsC`, `gsD`);
* `pre_class_le`: `gsC·(n+1)^gsD ≤ c_G·classBound E_G .preprocessing n k ψ` once `gsD ≤ E_G.Apre`,
  `gsC·2^gsD ≤ c_G`;
* **`gateSymAt`**: `GeoIface2.GateSymWriterAt l F E_G c_G kclk coef A a ha` (the machine `gsM DvS CvS`).

Paper quantity of the main type: C3a's gate field of the call's pool (P3:1655-1664) within the preprocessing class. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4GateSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.SupplierPipeline
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces NearCubicWires.ValidatorPolynomialDomination

/-! ## Monotone costs -/

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  omega

theorem gateCost_mono2 {h H n n' : ℕ} (hh : h ≤ H) (hn : n ≤ n') :
    C4Gates.gateCost h n ≤ C4Gates.gateCost H n' := by
  have a1 := C4Gates.pairCost_mono hh
  have a2 := nbl_mono hn
  unfold C4Gates.gateCost
  gcongr

theorem convCost_mono {n n' P P' H H' : ℕ} (hn : n ≤ n') (hP : P ≤ P') (hH : H ≤ H') :
    C4Gates.convCost n P H ≤ C4Gates.convCost n' P' H' := by
  have a1 := nbl_mono hn
  have a2 := nbl_mono hP
  have a3 := gateCost_mono2 hH hn
  unfold C4Gates.convCost
  gcongr

/-! ## The fill count -/

/-- What the data stage asks of its unary counts `1^L = 1^W` at a call of length `n` (the codes' bits, the circuit
and carrier envelopes). -/
def needW (n : ℕ) : ℕ :=
  4 * PrimAsm.CallSize.circBits (PrimAsm.CallSize.codeParam 26 26 n) +
    4 * PrimAsm.CallSize.carrierBits (PrimAsm.CallSize.codeParam 26 26 n) + 20 * (n + 1) ^ 26 + 4 * n + 20

theorem needW_pb : PolynomiallyBounded needW := by
  have hc := polynomiallyBounded_comp PrimAsm.CallSize.pb_circBits PrimAsm.CallSize.pb_codeParam
  have hk := polynomiallyBounded_comp PrimAsm.CallSize.pb_carrierBits PrimAsm.CallSize.pb_codeParam
  have h26 : PolynomiallyBounded (fun n : ℕ => (n + 1) ^ 26) :=
    polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 26
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4) hc)
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4) hk))
    (polynomiallyBounded_mul (polynomiallyBounded_constant 20) h26))
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4) polynomiallyBounded_id))
    (polynomiallyBounded_constant 20)

/-- The fill count's coefficient (`W = CvS·(n+1)^DvS`). -/
noncomputable def CvS : ℕ := Classical.choose needW_pb

/-- The fill count's degree. -/
noncomputable def DvS : ℕ := Classical.choose (Classical.choose_spec needW_pb)

theorem needW_le (n : ℕ) : needW n ≤ UnaryCalc.value DvS CvS n :=
  (Classical.choose_spec (Classical.choose_spec needW_pb)).2 n

/-! ## The data stage's hypotheses at a call -/

theorem nbl_small (x : ℕ) (hx : x ≤ 4) : 2 ^ (natBitLength x + 1) ≤ 16 := by
  have h1 : natBitLength x ≤ 3 := by
    unfold natBitLength
    have a := Nat.log_mono_right (b := 2) hx
    have b : Nat.log 2 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.log_pow (by norm_num)]
    omega
  calc 2 ^ (natBitLength x + 1) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 16 := by norm_num

theorem unaryList_len_le (cs : List ℕ) (B : ℕ) (h : ∀ c ∈ cs, c ≤ B) :
    (PrimAsm.Data.unaryList cs).length ≤ cs.length * (B + 1) := by
  unfold PrimAsm.Data.unaryList
  apply PrimAsm.CallSize.flatMap_length_le
  intro c hc
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  have := h c hc
  omega

section Data
variable {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **PA's data stage's hypotheses** at `W ≥ needW n`, from the call's envelopes. -/
theorem sym_data_hyps (ha : a' ≤ 4) (hk : carriers.length ≤ 2) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26)
    (he : ∀ X ∈ carriers, X.WithinEnvelope 26) (W : ℕ) (hW : needW n ≤ W) :
    (∀ i, (Cs i).descriptionBits ≤ W) ∧ (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ W) ∧ 2 ≤ n + W ∧
    natBitLength n + 1 ≤ 2 * W + 2 ∧ 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2 ∧
    2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2 ∧
    (∀ x ∈ PrimAsm.Data.symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + W ≤ 2 * W + 2) ∧
    (∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + W ≤ 2 * W + 2) ∧
    2 * (PrimAsm.Data.unaryList (carriers.map (·.length))).length +
      2 * (PrimAsm.Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2 ∧
    (∀ i, natBitLength (encodeNormalizedSymmetricThresholdCircuit (Cs i)) ≤ W) ∧
    (∀ X ∈ carriers, natBitLength X.code ≤ W) := by
  obtain ⟨p, hp⟩ : ∃ p, p = PrimAsm.CallSize.codeParam 26 26 n := ⟨_, rfl⟩
  have hpd : p = (n + 1) ^ 26 + (n + 1) ^ 26 + n + 4 := by rw [hp]; rfl
  have hWd : 4 * PrimAsm.CallSize.circBits p + 4 * PrimAsm.CallSize.carrierBits p + 20 * (n + 1) ^ 26 + 4 * n + 20 ≤
      W := by rw [hp]; exact hW
  have hcb : ∀ i, natBitLength (encodeNormalizedSymmetricThresholdCircuit (Cs i)) ≤ PrimAsm.CallSize.circBits p :=
    fun i => PrimAsm.CallSize.code_bits_le .sym (Cs i) p (by omega)
      (by have := hd i; show (Cs i).descriptionBits ≤ p; omega)
  have hkb : ∀ X ∈ carriers, natBitLength X.code ≤ PrimAsm.CallSize.carrierBits p :=
    fun X hX => PrimAsm.CallSize.carrier_bits_le X 26 p (he X hX) (by omega)
  have hnN := PrimAsm.CopyNat.natBitLength_le_self_succ n
  refine ⟨fun i => by have := hd i; omega, fun X hX g hg => by have := (he X hX).2 g hg; omega, by omega,
    by omega, by have := nbl_small a' ha; omega, by have := nbl_small carriers.length (by omega); omega,
    fun x hx => ?_, fun y hy => ?_, ?_, fun i => by have := hcb i; omega, fun X hX => by have := hkb X hX; omega⟩
  · unfold PrimAsm.Data.symCodes at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have := PrimAsm.CallSize.natWord_len_le (hcb i)
    omega
  · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hy
    have := PrimAsm.CallSize.natWord_len_le (hkb X hX)
    omega
  · have u1 := unaryList_len_le (carriers.map (·.length)) ((n + 1) ^ 26) (by
      intro c hc
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc
      exact (he X hX).1)
    have u2 := unaryList_len_le (List.ofFn fun i => (Stars.symGates (Cs i)).length) ((n + 1) ^ 26) (by
      intro c hc
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact PrimAsm.Data.symGates_len_le (Cs i) _ (hd i))
    rw [List.length_map] at u1
    rw [List.length_ofFn] at u2
    have v1 := Nat.mul_le_mul_right ((n + 1) ^ 26 + 1) hk
    have v2 := Nat.mul_le_mul_right ((n + 1) ^ 26 + 1) ha
    omega

/-! ## The pool's size and the slots' widths -/

theorem gatesW_len (h : ℕ) (G : List (NormalizedThresholdGate n)) :
    G.length ≤ (FinalPass.Corner.gatesW h G).length ∧ (G ≠ [] → h ≤ (FinalPass.Corner.gatesW h G).length) := by
  have hg : ∀ g : NormalizedThresholdGate n, h + 1 ≤ (FinalPass.Corner.gateW h g).length := by
    intro g
    unfold FinalPass.Corner.gateW
    rw [List.length_cons, List.length_append, C4Gates.pairW_length]
    omega
  have hf : G.length ≤ (G.flatMap (FinalPass.Corner.gateW h)).length := by
    induction G with
    | nil => simp
    | cons g G ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have := hg g
      omega
  unfold FinalPass.Corner.gatesW
  rw [List.length_append]
  refine ⟨by omega, fun hG => ?_⟩
  obtain ⟨g, G', rfl⟩ := List.exists_cons_of_ne_nil hG
  rw [List.flatMap_cons, List.length_append]
  have := hg g
  omega

theorem maskGates_nil (X : Stars.Carrier n) (h : FinalPass.Corner.maskGates X = []) : X = [] := by
  cases X with
  | nil => rfl
  | cons g X => simp [FinalPass.Corner.maskGates] at h

theorem gsH_nil (j : Fin 6) (h : gsG Cs carriers j = []) : gsH Cs carriers j = 1 := by
  by_cases h2 : j.val < 2
  · by_cases hk : j.val < carriers.length
    · rw [gsG_car Cs carriers j h2 hk] at h
      rw [gsH_car Cs carriers j h2 hk, maskGates_nil _ h]
      rfl
    · exact gsH_carE Cs carriers j h2 (by omega)
  · by_cases hi : j.val - 2 < a'
    · rw [gsG_sym Cs carriers j h2 hi] at h
      rw [gsH_sym Cs carriers j h2 hi, h]
      rfl
    · exact gsH_symE Cs carriers j h2 (by omega)

/-- **The pool's size and the slots' widths are at most `6·DC`**: every table is written within the data stage's
`DC` steps. -/
theorem pool_bounds (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ PrimAsm.Data.symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (carriers.map (·.length))).length +
      2 * (PrimAsm.Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2) :
    (PrimAsm.Records.symPool Cs carriers).length ≤ 6 * (2 * PrimAsm.Data.coreCost a' Cs carriers L W + 2) ∧
    gsHs Cs carriers ≤ 6 * (2 * PrimAsm.Data.coreCost a' Cs carriers L W + 2) + 6 := by
  obtain ⟨tout, m, sD, _, _, f1, f2, f3, f4⟩ := PrimAsm.Data.data_step_blank a' Cs carriers tl L W ha hk hL hLX h2
    hcN hcA hcK hcx hcy hcu
  obtain ⟨DC, hDC⟩ : ∃ x, x = 2 * PrimAsm.Data.coreCost a' Cs carriers L W + 2 := ⟨_, rfl⟩
  rw [← hDC] at sD ⊢
  have hlen : ∀ j : Fin 6, (tout (sTape (tabStream j))).length ≤ DC := by
    intro j
    obtain ⟨r, hr, _, hT, hs⟩ := sD
    have hv := tabStream_val j
    have hpos : 17 ≤ (tabStream j).val := by rw [hv]; split_ifs <;> omega
    have hne : ∀ s : Fin (PrimAsm.Data.DS + 1), s.val ≤ 3 →
        sTape (nr := PrimAsm.Data.DR) (tabStream j) ≠ sTape s :=
      fun s hs e => by have := congrArg Fin.val (sTape_inj e); omega
    have h0 := DecompositionSource.one_tape_support _ _ _ r (dPos (tabStream j)) 0 hr (le_refl _) (by
      show (Fin.addCases (motive := fun _ => List Bool)
        (PrimAsm.Data.rawIn (PrimAsm.Data.reqW n false (PrimAsm.Data.symCodes a' Cs)
          (carriers.map Stars.Carrier.code) tl) n L W)
        (fun _ : Fin 1 => List.replicate 0 false) (dPos (tabStream j))).length ≤ 0
      rw [addCases_dPos]
      unfold PrimAsm.Data.rawIn
      rw [if_neg (hne PrimAsm.Data.sIN (by decide)), if_neg (hne PrimAsm.Data.sNT (by decide)),
        if_neg (hne PrimAsm.Data.sLT (by decide)), if_neg (hne PrimAsm.Data.sCT (by decide))]
      simp)
    rw [hT] at h0
    simp only [addCases_dPos] at h0
    omega
  have hG : ∀ j, (gsG Cs carriers j).length ≤ DC ∧ gsH Cs carriers j ≤ DC + 1 := by
    intro j
    by_cases hn : gsG Cs carriers j = []
    · refine ⟨by rw [hn]; simp, by rw [gsH_nil Cs carriers j hn]; omega⟩
    · rcases slot_T Cs carriers tout f1 f2 f3 f4 j with e | ⟨_, e⟩
      · have hl := hlen j
        rw [e] at hl
        obtain ⟨g1, g2⟩ := gatesW_len (gsH Cs carriers j) (gsG Cs carriers j)
        have := g2 hn
        omega
      · exact absurd e hn
  have hsum : (PrimAsm.Records.symPool Cs carriers).length = (gsG Cs carriers 0).length +
      (gsG Cs carriers 1).length + (gsG Cs carriers 2).length + (gsG Cs carriers 3).length +
      (gsG Cs carriers 4).length + (gsG Cs carriers 5).length := by
    rw [symPool_eq Cs carriers ha hk, allJ_flatMap]
    simp only [List.length_append]
  obtain ⟨a0, b0⟩ := hG 0
  obtain ⟨a1, b1⟩ := hG 1
  obtain ⟨a2, b2⟩ := hG 2
  obtain ⟨a3, b3⟩ := hG 3
  obtain ⟨a4, b4⟩ := hG 4
  obtain ⟨a5, b5⟩ := hG 5
  refine ⟨by rw [hsum]; omega, by unfold gsHs; omega⟩

end Data

/-! ## The writer's steps -/

/-- The front's steps' bound at length `n`. -/
noncomputable def frontCn (n : ℕ) : ℕ :=
  2 * (2 * PrimAsm.CallSize.wordBound 26 26 2 n + 1) + 2 + 1 + (2 * (8 * n + 20 * natBitLength n + 17) + 2) + 1 +
    PCPSerializerCapacity.Power.budget DvS CvS n

/-- The data stage's steps' bound at length `n` (`coreCost_poly`). -/
noncomputable def DCn (n : ℕ) : ℕ :=
  PrimAsm.Data.symCc * (UnaryCalc.value DvS CvS n + n + UnaryCalc.value DvS CvS n + UnaryCalc.value DvS CvS n + 1) ^
    PrimAsm.Data.symDc

/-- **The writer's steps' bound at length `n`.** -/
noncomputable def costN (n : ℕ) : ℕ :=
  2 * (frontCn n + 1 + (2 * (UnaryCalc.value DvS CvS n * 7 + 1 + 1 + (n * 7 + 1)) + 2) + 1 + DCn n + 1 +
    (2 * C4Gates.convCost n (6 * DCn n) (6 * DCn n + 6) + 2)) + 2

theorem cost_le (w : List Bool) (n DC P H : ℕ) (hw : w.length ≤ PrimAsm.CallSize.wordBound 26 26 2 n)
    (hDC : DC ≤ DCn n) (hP : P ≤ 6 * DC) (hH : H ≤ 6 * DC + 6) :
    2 * gsCost w n DvS CvS DC P H + 2 ≤ costN n := by
  have hc := convCost_mono (le_refl n) (show P ≤ 6 * DCn n by omega) (show H ≤ 6 * DCn n + 6 by omega)
  unfold gsCost frontC costN frontCn
  omega

/-- The converter's cost with every bit length by its bound `x + 1`. -/
def convMaj (n P H : ℕ) : ℕ :=
  n * 7 + 1 + ((n + 1) + 10) * (100 * n + 200) + (23 * (4 * (n + 1) + 2) + 4) +
    ((P + 6) * ((n + 2) * (20 * H * H + 700 * H + 700 + 100) + 300 * ((n + 1) + 1) + 500 * H + 800 + 4) + 12) +
    ((P + 1) + 10) * (100 * P + 200) + (61 * n + 5) + 16 +
    (46 * (P * ((8 * H + 8) * (n + 2) + 8 * (n + 1) + 8)) + 5) + 8 + 20

theorem convCost_le_maj (n P H : ℕ) : C4Gates.convCost n P H ≤ convMaj n P H := by
  have a1 := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have a2 := PrimAsm.CopyNat.natBitLength_le_self_succ P
  unfold C4Gates.convCost convMaj C4Gates.gateCost C4Gates.pairCost
  gcongr

theorem pb_value : PolynomiallyBounded (fun n => UnaryCalc.value DvS CvS n) :=
  polynomiallyBounded_mul (polynomiallyBounded_constant CvS)
    (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) DvS)

theorem pb_DCn : PolynomiallyBounded DCn :=
  polynomiallyBounded_mul (polynomiallyBounded_constant _)
    (polynomiallyBounded_pow (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add pb_value polynomiallyBounded_id) pb_value) pb_value) (polynomiallyBounded_constant 1)) _)

theorem pb_nbl : PolynomiallyBounded (fun n => natBitLength n) :=
  polynomiallyBounded_mono (fun n => PrimAsm.CopyNat.natBitLength_le_self_succ n)
    (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1))

theorem pb_power : PolynomiallyBounded (fun n => PCPSerializerCapacity.Power.budget DvS CvS n) := by
  apply polynomiallyBounded_mono
    (larger := fun n => 2 * n + 9 + (2 * CvS + 2 + DvS * (10 * CvS * (n + 1) ^ DvS + 7)))
  · intro n
    have := MatrixPacketCapacityCost.power_cost DvS CvS (n + 1) DvS (by omega) (le_refl _)
    unfold PCPSerializerCapacity.Power.budget
    omega
  · iterate 40 (all_goals (try (first
      | with_reducible exact polynomiallyBounded_id
      | with_reducible exact polynomiallyBounded_constant _
      | with_reducible apply polynomiallyBounded_add
      | with_reducible apply polynomiallyBounded_mul
      | with_reducible apply polynomiallyBounded_pow)))

theorem pb_conv : PolynomiallyBounded (fun n => C4Gates.convCost n (6 * DCn n) (6 * DCn n + 6)) := by
  apply polynomiallyBounded_mono (fun n => convCost_le_maj n (6 * DCn n) (6 * DCn n + 6))
  unfold convMaj
  iterate 40 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible exact pb_value
    | with_reducible exact pb_DCn
    | with_reducible exact pb_nbl
    | with_reducible exact pb_power
    | with_reducible exact PrimAsm.CallSize.wordBound_poly
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

theorem pb_costN : PolynomiallyBounded costN := by
  have hc := pb_conv
  show PolynomiallyBounded (fun n => costN n)
  simp only [costN, frontCn]
  iterate 40 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible exact pb_value
    | with_reducible exact pb_DCn
    | with_reducible exact pb_nbl
    | with_reducible exact pb_power
    | with_reducible exact hc
    | with_reducible exact PrimAsm.CallSize.wordBound_poly
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

/-- The writer's steps' coefficient. -/
noncomputable def gsC : ℕ := Classical.choose pb_costN

/-- The writer's steps' degree. -/
noncomputable def gsD : ℕ := Classical.choose (Classical.choose_spec pb_costN)

theorem costN_le (n : ℕ) : costN n ≤ gsC * (n + 1) ^ gsD :=
  (Classical.choose_spec (Classical.choose_spec pb_costN)).2 n

/-! ## The writer at every SYM call -/

/-- A machine and its distinct ports as a `WriterStage`. -/
def mkStage {t s : ℕ} (M : Machine t s) (i o : Fin t) (h : i ≠ o) : PrimAsm.WriterIface.WriterStage :=
  ⟨t, s, M, i, o, h⟩

/-- A run of the machine is a run of its stage (stated with the stage's own fields, so a structure built from
`mkStage` takes it without unfolding the machine's tape count). -/
theorem stage_run {t s : ℕ} (M : Machine t s) (i o : Fin t) (h : i ≠ o) (B : ℕ) (w v : List Bool)
    (hr : PrimAsm.WriterIfaceJ.WriterRun M B i o w v) :
    PrimAsm.WriterIfaceJ.WriterRun (mkStage M i o h).M B (mkStage M i o h).inS (mkStage M i o h).outS w v := hr

section Ready
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **Into the preprocessing class**: `C·(n+1)^D ≤ c_G·2^(cψ·ψ)·n^Apre` once `D ≤ Apre` and `C·2^D ≤ c_G`. -/
theorem pre_class_le (EG : Envelope) (C D cG n k psi : ℕ) (hn : 1 ≤ n) (hA : D ≤ EG.Apre) (hc : C * 2 ^ D ≤ cG) :
    C * (n + 1) ^ D ≤ cG * classBound EG .preprocessing n k psi := by
  have h1 : (n + 1) ^ D ≤ 2 ^ D * n ^ D := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) D
  have h2 : n ^ D ≤ n ^ EG.Apre := Nat.pow_le_pow_right hn hA
  have h3 : 1 ≤ 2 ^ (EG.cpsi * psi) := Nat.one_le_two_pow
  show C * (n + 1) ^ D ≤ cG * (2 ^ (EG.cpsi * psi) * n ^ EG.Apre)
  calc C * (n + 1) ^ D ≤ C * (2 ^ D * n ^ D) := Nat.mul_le_mul_left _ h1
    _ = (C * 2 ^ D) * n ^ D := by ring
    _ ≤ cG * n ^ EG.Apre := Nat.mul_le_mul hc h2
    _ ≤ cG * (2 ^ (EG.cpsi * psi) * n ^ EG.Apre) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))

variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem sym_call_facts (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (h : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation)) :
    carriers.length ≤ 2 ∧ (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) ∧ (∀ X ∈ carriers, X.WithinEnvelope 26) := by
  obtain ⟨_, hcar, hdesc, hcount, _, _, _⟩ := h
  exact ⟨hcount, fun i => hdesc i, hcar⟩

/-- **The SYM gate-frame writer's run at every SYM call of the family**, within the preprocessing class. -/
theorem gs_ready (hA : gsD ≤ EG.Apre) (hc : gsC * 2 ^ gsD ≤ cG) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PrimAsm.WriterIfaceJ.WriterRun (mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).M
      (cG * classBound EG .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n))
      (mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).inS
      (mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).outS
      (symReq n a' ha' Cs carriers translation).word (C4Geo.gateField (PrimAsm.Records.symPool Cs carriers)) := by
  refine stage_run (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS) _ _ _ ?_
  obtain ⟨hk, hd, he⟩ := sym_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  have hn : 1 ≤ n := by
    have h1 := hs.2.1
    have h2 := hs.2.2.1
    omega
  obtain ⟨hL, hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu, hK, hKX⟩ :=
    sym_data_hyps Cs carriers ha' hk hd he (UnaryCalc.value DvS CvS n) (needW_le n)
  have hword := PrimAsm.ReqBridge.reqW_symReq ha' Cs carriers translation
  rw [← hword]
  refine gs_run DvS CvS _ n a' Cs carriers _ ha' hk _ rfl hL hLX h2 hcN hcA hcK hcx hcy hcu ?_
  obtain ⟨hP, hH⟩ := pool_bounds Cs carriers (RepairRepresentation.natListWord translation) _ _ ha' hk hL hLX h2
    hcN hcA hcK hcx hcy hcu
  have hDC := PrimAsm.Data.coreCost_poly Cs carriers (UnaryCalc.value DvS CvS n) (UnaryCalc.value DvS CvS n)
    (UnaryCalc.value DvS CvS n) ha' hk hL hLX hK hKX h2
  have hwl : (PrimAsm.Data.reqW n false (PrimAsm.Data.symCodes a' Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation)).length ≤ PrimAsm.CallSize.wordBound 26 26 2 n := by
    rw [hword]
    exact PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha _ hcall
  have c1 := cost_le _ n _ _ _ hwl (by unfold DCn; exact hDC) hP hH
  have c2 := costN_le n
  have c3 := pre_class_le EG gsC gsD cG n (((gate0 l F).budget kclk coef A a ha).kOf n)
    (((gate0 l F).budget kclk coef A a ha).psiOf n) hn hA hc
  omega

/-- **The SYM gate-frame writer** (`GeoIface2.GateSymWriterAt`): the machine `gsM DvS CvS`, from
`frame (symReq …).word` to C3a's gate field of the call's pool, at every call of the family. -/
noncomputable def gateSymAt (hA : gsD ≤ EG.Apre) (hc : gsC * 2 ^ gsD ≤ cG) :
    GeoIface2.GateSymWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS), fun n a' ha' Cs carriers translation hcall hs =>
    gs_ready l F EG cG kclk coef A a ha hA hc n a' ha' Cs carriers translation hcall hs⟩

end Ready

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym
