import Proof.Wire_3_5.UnionMachine.CWBounds
import Proof.Wire_3_5.UnionMachine.CWIface
import Proof.Wire_3_5.Primitive.SeedFix.CarrierFormat

/-! # C6 front, U5, the code writers: the carrier writer of the `SYM∘THR` mode

"It then selects the common star translation, constructs the shared coordinate filters" (P3:3673-3674): the union
front writes each call's named carrier `Stars.Carrier.code (carrierOf .sym cs)` from the codes of the circuits it
collects. The charged gates of a `SYM∘THR` circuit are ALL its bottoms (`Stars.symGates`), so the core machine's
output is exactly the carrier code:
* a circuit's bottoms field is the balanced list of its bottoms' codes (`fld_sym`, base's circuit header on
  `encodeNormalizedSymmetricThresholdCircuit`), so loop A collects the bottoms' codes (`bw_sym`);
* a bottom word's atom code `gc` is `gateCode` of its gate (`gc_bottom`, from
  `CarrierFormat.supported_codeWords`);
* **`code_sym`**: the serializer's code of the atom codes is `Carrier.code (carrierOf .sym cs)`;
* **`symWriter : CarrierWriterJ .sym`**, within `(Kc + 3)·(|u| + q + 1)^26`, residue bounded by the same.

Paper quantity of the main type: the code of the named carrier of a list of `SYM∘THR` circuits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.CanonicalBinary
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords NearCubicWires.WireExponent3_5.UnionMachine.CWCore
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain NearCubicWires.WireExponent3_5.UnionMachine.CWBounds
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters NearCubicWires.WireExponent3_5.UnionMachine.CWIface
open NearCubicWires.WireExponent3_5.PrimT.CarrierFormat (gateCode)

/-! ## From codes to bottoms -/

/-- The bottoms field of a circuit whose code is a tagged list `[a, b, c, d]` has value `c`. -/
theorem fld_value (x a b c d : ℕ) (h : x = encodeTaggedList [a, b, c, d]) : value (CWRoundA.fld x) = c := by
  have := CloseoutRowsCircuitHeader.code_values a b c d (pay x) (by rw [value_pay, h]) 2
  show value (CloseoutRowsCircuitHeader.codeWord (pay x) 2) = c
  simpa using this

/-- **Loop A collects a bottom's codes**: the atoms of a circuit's bottoms field are its bottoms' codes. -/
theorem bw_of (x : ℕ) (l : List ℕ) (h : value (CWRoundA.fld x) = encodeBalancedList l) :
    CWRoundA.bw x = l.map (binary (CWRoundA.fld x).length) := by
  unfold CWRoundA.bw
  rw [h, PCPPNativeCanonicalTree.tree_atoms]

/-- The atoms are below `2 ^ width`. -/
theorem atom_lt (x : ℕ) (l : List ℕ) (h : value (CWRoundA.fld x) = encodeBalancedList l) (b : ℕ) (hb : b ∈ l) :
    b < 2 ^ (CWRoundA.fld x).length := by
  have hv := RadixSemantics.value_lt (CWRoundA.fld x)
  rw [h] at hv
  exact lt_of_le_of_lt (CloseoutWitness.Reencode.atom_le _ b (by rw [PCPPNativeCanonicalTree.tree_atoms]; exact hb)) hv

/-- **A bottom word's atom code is the gate code of its gate.** -/
theorem gc_bottom {n : ℕ} (W : ℕ) (sg : SupportedNormalizedGate n) (hlt : encodeSupportedNormalizedGate sg < 2 ^ W) :
    CWRoundB.gc (binary W (encodeSupportedNormalizedGate sg)) = gateCode sg.gate := by
  unfold CWRoundB.gc CWRoundB.cw
  rw [PrimT.CarrierFormat.supported_codeWords sg _ (binary_value _ _ hlt)]

/-! ## The `SYM∘THR` circuits -/

theorem fld_sym {q : ℕ} (C : NormalizedSymmetricThresholdCircuit q) :
    value (CWRoundA.fld (encodeNormalizedSymmetricThresholdCircuit C)) =
      encodeBalancedList (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)) :=
  fld_value _ (encodeNat symmetricCircuitFamilyTag) (encodeNat C.bottomCount) _ (encodeBoolList (List.ofFn C.top)) rfl

/-- A list of bottoms, word by word: each atom code is its gate's code. -/
theorem map_gc {n : ℕ} (W : ℕ) : ∀ (sgs : List (SupportedNormalizedGate n)),
    (∀ sg ∈ sgs, encodeSupportedNormalizedGate sg < 2 ^ W) →
    (sgs.map encodeSupportedNormalizedGate).map (CWRoundB.gc ∘ binary W) =
      sgs.map fun sg => gateCode sg.gate
  | [], _ => rfl
  | sg :: sgs, h => by
    rw [List.map_cons, List.map_cons, List.map_cons, Function.comp_apply, gc_bottom W sg (h sg (by simp)),
      map_gc W sgs (fun t ht => h t (by simp [ht]))]

theorem bw_gc_sym {q : ℕ} (C : NormalizedSymmetricThresholdCircuit q) :
    (CWRoundA.bw (encodeNormalizedSymmetricThresholdCircuit C)).map CWRoundB.gc = (Stars.symGates C).map gateCode := by
  have hf := fld_sym C
  have hl : (List.ofFn fun i => encodeSupportedNormalizedGate (C.bottom i)) =
      (List.ofFn C.bottom).map encodeSupportedNormalizedGate := by rw [List.map_ofFn]; rfl
  rw [hl] at hf
  have hg : (Stars.symGates C).map gateCode = (List.ofFn C.bottom).map fun sg => gateCode sg.gate := by
    rw [PrimT.CarrierFormat.symGates_codes, List.map_ofFn]; rfl
  rw [bw_of _ _ hf, List.map_map, hg]
  exact map_gc _ _ (fun sg hsg => atom_lt _ _ hf _ (List.mem_map_of_mem hsg))

theorem bots_gc_sym {q : ℕ} (cs : List (NormalizedSymmetricThresholdCircuit q)) :
    (bots (cs.map (Mode.code .sym))).map CWRoundB.gc = (carrierOf .sym cs).map gateCode := by
  rw [bots_eq, List.map_flatten, List.map_map, List.map_map]
  unfold carrierOf
  rw [List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro C _
  exact bw_gc_sym C

theorem values_bits (f : List Bool → ℕ) : ∀ l : List (List Bool),
    (l.map fun y => (f y).bits).map RadixSemantics.value = l.map f
  | [] => rfl
  | y :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, CanonicalPositiveOutput.nat_bits_value, values_bits f l]

/-- **The serializer's code is the carrier code.** -/
theorem code_sym {q : ℕ} (cs : List (NormalizedSymmetricThresholdCircuit q)) :
    PCPTraversal.code (codes (cs.map (Mode.code .sym))) = Stars.Carrier.code (carrierOf .sym cs) := by
  have h1 : PCPTraversal.code (codes (cs.map (Mode.code .sym))) =
      encodeBalancedList ((codes (cs.map (Mode.code .sym))).map RadixSemantics.value) := rfl
  rw [h1, codes_eq, values_bits, bots_gc_sym]
  exact (PrimT.CarrierFormat.code_eq _).symm

/-! ## The writer -/

theorem codesWord_sym {q : ℕ} (cs : List (NormalizedSymmetricThresholdCircuit q)) :
    codesWord .sym cs = ((cs.map (Mode.code .sym)).map natWord).flatten := by
  unfold codesWord; rw [List.map_map]; rfl

theorem inBank_eq (u : List Bool) : inBank (0 : Fin 913) u = coreIn u := by
  funext j; unfold inBank coreIn
  by_cases h : j = 0
  · subst h; simp
  · have h' : ¬ j.val = 0 := fun e => h (Fin.ext e)
    rw [if_neg h, if_neg h']

theorem outBank_eq (u v : List Bool) (tout : Fin 913 → List Bool) (h0 : tout 0 = frame u) (h1 : tout 1 = frame v) :
    outBankJ 0 1 u v tout = tout := by
  funext j; unfold outBankJ
  by_cases e0 : j = 0
  · subst e0; simp [h0]
  · by_cases e1 : j = 1
    · subst e1; simp [h1]
    · simp [e0, e1]

/-- **The `SYM∘THR` carrier writer's run.** -/
theorem sym_ready (q : ℕ) (cs : List (NormalizedSymmetricThresholdCircuit q)) :
    ∃ J : Fin 913 → List Bool, (∀ j, (J j).length ≤ (Kc + 3) * ((codesWord .sym cs).length + q + 1) ^ 26) ∧
      ClockJoin.ReadyRun coreM ((Kc + 3) * ((codesWord .sym cs).length + q + 1) ^ 26) (inBank 0 (codesWord .sym cs))
        (outBankJ 0 1 (codesWord .sym cs) (natWord (Stars.Carrier.code (carrierOf .sym cs))) J) := by
  have hu : codesWord .sym cs = ((cs.map (Mode.code .sym)).map natWord).flatten := codesWord_sym cs
  obtain ⟨tout, st, h0, h1⟩ := core_step (cs.map (Mode.code .sym)) (caps_ok _)
  have hcost := coreCost_le (cs.map (Mode.code .sym))
  rw [code_sym cs] at h1
  rw [← hu] at h0 hcost st
  have hr := FrontKit.ready_of_step st
  generalize codesWord .sym cs = u at *
  have hP1 : (u.length + 1) ^ 26 ≤ (u.length + q + 1) ^ 26 := Nat.pow_le_pow_left (by omega) _
  have hP2 : u.length + 1 ≤ (u.length + q + 1) ^ 26 :=
    (Nat.le_self_pow (by norm_num) _).trans hP1
  have hlen := NearCubicWires.WireExponent3_5.Transfer.ready_lengths hr (2 * u.length + 1) (by
    intro i; unfold coreIn; split_ifs
    · rw [frame_eq_frameP]; simp
    · simp)
  generalize (u.length + q + 1) ^ 26 = P at *
  have h1' := Nat.mul_le_mul_left Kc hP1
  have e : (Kc + 3) * P = Kc * P + 3 * P := by ring
  refine ⟨tout, fun j => ?_, ?_⟩
  · have := hlen j
    rw [e]; omega
  · rw [inBank_eq, outBank_eq _ _ tout h0 h1]
    exact ClockJoin.enlarge _ _ _ _ _ hr (by rw [e]; omega)

end NearCubicWires.WireExponent3_5.UnionMachine.CWSym
