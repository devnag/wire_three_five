import Proof.Wire_3_5.Primitive.ThresholdWriter.PortsE
import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Port
import Proof.Wire_3_5.Primitive.Writers.ThrDataCost

/-! # TopFrontPort3 body, part 8: the cost is polynomial in `V`, and the front end (`topFront3`)

P3:3071-3091 and P3:2543-2551 in the port form of W16 (`PortsE.TopFrontPort3`): the front end's cost is `PolyBounded` in
its count `V`. At `a' = 0` it pays only the fill and the guard (linear in `V`: `TF2Ok` bounds `n`'s bit length); at
`a' ≥ 1`, `TF2Ok` gives `(n+1)^26 ≤ 2V`, so the word stage is quadratic in `V`, the decode block is
`≤ c_B(5(V+1))^{d_B}` (`TabCost.thrBlock_poly`) and the top decomposition is `≤ (2052k + 40)(S+1)^{E}` with
`S = |thrWord c| ≤ 1088(V+1)^2` (`TabCost.thrWord_pb`, base's `SelOrigCost.entry_le`/`output_le`, `k = (coef+2)^2`,
`E = thrOE a`).

* `cB`, `dB`, `block_le`; **`top_le`**; `D3`, `C3`; **`fuel_le`** (`2·innerFuel + 3 ≤ C3·(V+1)^{D3}`);
* **`topFront3 alg : PortsE.TopFrontPort3 alg`**: the THR front end on ports, every `a' ≤ 4` (W16).

Paper quantities of the main type: each circuit's retained-top children (`payOf`) and native word, on ports. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Cost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimThrW.TF3Run NearCubicWires.ValidatorPolynomialDomination

/-! ## The decode block -/

/-- The block coefficient. -/
noncomputable def cB : ℕ := Classical.choose TabCost.thrBlock_poly
/-- The block degree. -/
noncomputable def dB : ℕ := Classical.choose (Classical.choose_spec TabCost.thrBlock_poly)

theorem block_le {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (L K : ℕ) (hL : C.descriptionBits ≤ L)
    (hK : natBitLength (encodeNormalizedThresholdThresholdCircuit C) ≤ K) :
    ThrTab.thrBlockCost C L ≤ cB * (K + n + L + 1) ^ dB :=
  Classical.choose_spec (Classical.choose_spec TabCost.thrBlock_poly) C L K hL hK

theorem nbl_le_succ (x : ℕ) : natBitLength x ≤ x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [natBitLength]
  · have := nbl_le x hx; omega

/-! ## The top decomposition -/

variable (a : DecompositionAlgorithm)

/-- **The top decomposition's budget** at a circuit whose native word has at most `S` bits. -/
theorem top_le {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) (S : ℕ)
    (hS : (PCJd4d1d9d7d1fa4313_Production.thrWord c).length ≤ S) :
    PayM.topBudget a c ≤ (2052 * (a.coefficient + 2) ^ 2 + 40) * (S + 1) ^ SourceRequest.SelOrigCost.thrOE a +
      4 * c.top.wireCount := by
  have hp := (TabCost.thrWord_parts c).2.1
  have htw := DecompositionSource.thresholdWord_length (CompilerSemantics.nonStrictAsStrict (retainedTopGate c))
  have hen := SourceRequest.SelOrigCost.entry_le a ⟨c.top.support.card,
    CompilerSemantics.nonStrictAsStrict (retainedTopGate c)⟩ S (by
      show c.top.support.card + (CompilerSemantics.nonStrictAsStrict (retainedTopGate c)).encodingBits + 1 ≤ S + 1
      omega)
  have hou := SourceRequest.SelOrigCost.output_le a ⟨c.top.support.card,
    CompilerSemantics.nonStrictAsStrict (retainedTopGate c)⟩ S (by
      show c.top.support.card + (CompilerSemantics.nonStrictAsStrict (retainedTopGate c)).encodingBits + 1 ≤ S + 1
      omega) (by show 2 * natBitLength c.top.support.card + 1 ≤ S + 1; omega)
  have hl := SourceRequest.SelOrigCost.lin_le S (SourceRequest.SelOrigCost.thrOE a)
    (by unfold SourceRequest.SelOrigCost.thrOE; omega)
  have hw := nbl_le_succ c.top.wireCount
  have e : (2052 * (a.coefficient + 2) ^ 2 + 40) * (S + 1) ^ SourceRequest.SelOrigCost.thrOE a =
      2052 * ((a.coefficient + 2) ^ 2 * (S + 1) ^ SourceRequest.SelOrigCost.thrOE a) +
        40 * (S + 1) ^ SourceRequest.SelOrigCost.thrOE a := by ring
  rw [e]
  unfold PayM.topBudget PCJ6e421fabe2aa4155_SourceTopNative.budget PCJ6e421fabe2aa4155_SourceTopExtract.budget
    PCJ6e421fabe2aa4155_SourceTopExtract.rawBudget PCJ6e421fabe2aa4155_SourceTopEntry.budget
  dsimp only
  omega

/-! ## The fuel -/

/-- The front end's degree. -/
noncomputable def D3 : ℕ := dB + 2 * SourceRequest.SelOrigCost.thrOE a + 2

/-- The front end's coefficient. -/
noncomputable def C3 : ℕ :=
  10 ^ 7 + 8 * (cB * 5 ^ dB + (2052 * (a.coefficient + 2) ^ 2 + 40) * 1089 ^ SourceRequest.SelOrigCost.thrOE a + 100)

theorem two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * (x + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [natBitLength]
  · have := two_pow_nbl x hx; omega

theorem nbl_prod (x : ℕ) (hx : x ≤ 4) : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ 3080 := by
  have h1 := nbl_le_succ x
  have h2 := two_pow_nbl_le x
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ 7 * 440 :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = 3080 := by norm_num

/-- **One slot's cost**, once a circuit exists (`L = (n+1)^26 ≤ 2V`). -/
theorem slot_le {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (V : ℕ)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hok : TopFront2.TF2Ok Cs codes V)
    (h26 : (n + 1) ^ 26 ≤ 2 * V) (i : Fin 4) :
    TF3Slots.slotCost a ((n + 1) ^ 26) Cs i ≤ cB * 5 ^ dB * (V + 1) ^ dB +
      (2052 * (a.coefficient + 2) ^ 2 + 40) * 1089 ^ SourceRequest.SelOrigCost.thrOE a *
        (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a) + 8 * V + 3 := by
  unfold TF3Slots.slotCost
  split_ifs with h
  · set c := Cs ⟨i.val, h⟩ with hc
    have hn1 : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    have hx := hok.hcx (encodeNormalizedThresholdThresholdCircuit c) (by simp [ReqBridge.thrCodes, List.mem_ofFn, hc])
    have hK := ParseNat.natWord_length (encodeNormalizedThresholdThresholdCircuit c)
    have hb := block_le c ((n + 1) ^ 26) V (hd _) (by omega)
    have h5 : V + n + (n + 1) ^ 26 + 1 ≤ 5 * (V + 1) := by omega
    have hb' : ThrTab.thrBlockCost c ((n + 1) ^ 26) ≤ cB * 5 ^ dB * (V + 1) ^ dB := by
      calc ThrTab.thrBlockCost c ((n + 1) ^ 26) ≤ cB * (V + n + (n + 1) ^ 26 + 1) ^ dB := hb
        _ ≤ cB * (5 * (V + 1)) ^ dB := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 _)
        _ = cB * 5 ^ dB * (V + 1) ^ dB := by rw [mul_pow]; ring
    have hw := TabCost.thrWord_pb c ((n + 1) ^ 26) (n + (n + 1) ^ 26) (hd _) le_rfl
    unfold PolyBounded at hw
    have hS : (PCJd4d1d9d7d1fa4313_Production.thrWord c).length + 1 ≤ 1089 * (V + 1) ^ 2 := by
      have e : n + (n + 1) ^ 26 + 1 ≤ 4 * (V + 1) := by omega
      have e2 := Nat.pow_le_pow_left e 2
      have e3 : (4 * (V + 1)) ^ 2 = 16 * (V + 1) ^ 2 := by ring
      have e4 : 1 ≤ (V + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have ht := top_le a c _ le_rfl
    have hwc := (TabCost.thrWord_parts c).2.2
    have hdi : c.descriptionBits ≤ (n + 1) ^ 26 := hd _
    have hE : ((PCJd4d1d9d7d1fa4313_Production.thrWord c).length + 1) ^ SourceRequest.SelOrigCost.thrOE a ≤
        1089 ^ SourceRequest.SelOrigCost.thrOE a * (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a) := by
      calc ((PCJd4d1d9d7d1fa4313_Production.thrWord c).length + 1) ^ SourceRequest.SelOrigCost.thrOE a
          ≤ (1089 * (V + 1) ^ 2) ^ SourceRequest.SelOrigCost.thrOE a := Nat.pow_le_pow_left hS _
        _ = 1089 ^ SourceRequest.SelOrigCost.thrOE a * (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a) := by
          rw [mul_pow, ← pow_mul]
    have ht' := Nat.mul_le_mul_left (2052 * (a.coefficient + 2) ^ 2 + 40) hE
    have e5 : (2052 * (a.coefficient + 2) ^ 2 + 40) * (1089 ^ SourceRequest.SelOrigCost.thrOE a *
        (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a)) = (2052 * (a.coefficient + 2) ^ 2 + 40) *
          1089 ^ SourceRequest.SelOrigCost.thrOE a * (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a) := by ring
    rw [e5] at ht'
    omega
  · omega

theorem pow_mono_le (W j D : ℕ) (hW : 1 ≤ W) (hj : j ≤ D) : W ^ j ≤ W ^ D := Nat.pow_le_pow_right hW hj

/-- **The fuel is polynomial in `V`.** -/
theorem fuel_le {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (V : ℕ)
    (hn1 : 1 ≤ n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hok : TopFront2.TF2Ok Cs codes V) :
    2 * innerFuel a Cs codes V + 3 ≤ C3 a * (V + 1) ^ D3 a := by
  have hW1 : 1 ≤ V + 1 := by omega
  have hP1 : V + 1 ≤ (V + 1) ^ D3 a := by
    have := pow_mono_le (V + 1) 1 (D3 a) hW1 (by unfold D3; omega)
    simpa using this
  have hP2 : (V + 1) ^ 2 ≤ (V + 1) ^ D3 a := pow_mono_le (V + 1) 2 (D3 a) hW1 (by unfold D3; omega)
  have hPd : (V + 1) ^ dB ≤ (V + 1) ^ D3 a := pow_mono_le (V + 1) dB (D3 a) hW1 (by unfold D3; omega)
  have hPe : (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a) ≤ (V + 1) ^ D3 a :=
    pow_mono_le (V + 1) (2 * SourceRequest.SelOrigCost.thrOE a) (D3 a) hW1 (by unfold D3; omega)
  have eC : C3 a * (V + 1) ^ D3 a = 10 ^ 7 * (V + 1) ^ D3 a + 8 * (cB * 5 ^ dB * (V + 1) ^ D3 a) +
      8 * ((2052 * (a.coefficient + 2) ^ 2 + 40) * 1089 ^ SourceRequest.SelOrigCost.thrOE a * (V + 1) ^ D3 a) +
      800 * (V + 1) ^ D3 a := by
    unfold C3; ring
  rw [eC]
  have hT1P := Nat.mul_le_mul_left (cB * 5 ^ dB) hPd
  have hT2P := Nat.mul_le_mul_left
    ((2052 * (a.coefficient + 2) ^ 2 + 40) * 1089 ^ SourceRequest.SelOrigCost.thrOE a) hPe
  unfold innerFuel
  split_ifs with ha0
  · subst ha0
    have hN := hok.hcN
    unfold TF3Guard.gCost
    simp only [natBitLength, Nat.log_zero_right, Nat.zero_add, pow_one]
    unfold natBitLength at hN
    omega
  · have ha1 : 1 ≤ a' := by omega
    obtain ⟨h26, -, -, -, -⟩ := caps_of Cs codes V hn1 ha1 ha hok
    have hn1' : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
    have hW2 : V + 1 ≤ (V + 1) ^ 2 := by nlinarith
    have hg : TF3Guard.gCost n a' ≤ 2240 * (V + 1) := by
      unfold TF3Guard.gCost
      have := nbl_prod a' ha
      have := nbl_le n hn1
      omega
    have hA : TF3Prep.pACost n V ≤ 400 * (V + 1) ^ 2 := by
      unfold TF3Prep.pACost
      have h1 := nbl_le n hn1
      have h2 := two_pow_nbl n hn1
      have hm : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 320 * (V + 1) ^ 2 := by
        calc (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ (2 * (V + 1)) * (160 * (V + 1)) :=
              Nat.mul_le_mul (by omega) (by omega)
          _ = 320 * (V + 1) ^ 2 := by ring
      omega
    have hB : TF3Prep.pBCost n ((n + 1) ^ 26) (2 * V + 2) ≤ 346000 * (V + 1) ^ 2 := by
      unfold TF3Prep.pBCost UnaryPow.sq
      have hq : (2 * V + 2 + 2) * (2 * V + 2 + 2) ≤ 16 * (V + 1) ^ 2 := by
        calc (2 * V + 2 + 2) * (2 * V + 2 + 2) ≤ (4 * (V + 1)) * (4 * (V + 1)) :=
              Nat.mul_le_mul (by omega) (by omega)
          _ = 16 * (V + 1) ^ 2 := by ring
      have e1 : 200 * (2 * V + 2 + 2) * (2 * V + 2 + 2) = 200 * ((2 * V + 2 + 2) * (2 * V + 2 + 2)) := by ring
      simp only [List.length_singleton]
      rw [e1]
      have e2 : (n + 1) ^ 26 * (8 * 1 + 4) = 12 * (n + 1) ^ 26 := by ring
      have e3 : n * (8 * 1 + 4) = 12 * n := by ring
      rw [e2, e3]
      omega
    have hS : setupCost n ((n + 1) ^ 26) (ReqBridge.thrCodes Cs) codes ≤ 9000 * (V + 1) := by
      unfold setupCost
      have hx : ∀ x ∈ ReqBridge.thrCodes Cs, natBitLength x ≤ V := fun x hxm => by
        have := hok.hcx x hxm
        have := ParseNat.natWord_length x
        omega
      have hy : ∀ y ∈ codes, natBitLength y ≤ V := fun y hym => by
        have := hok.hcy y hym
        have := ParseNat.natWord_length y
        omega
      have b1 := ThrData.blocksCost_le n ((n + 1) ^ 26) V symTrips (ReqBridge.thrCodes Cs) hx
      have b2 := ThrData.blocksCost_le n ((n + 1) ^ 26) V carTrips codes hy
      have l1 : symTrips.length = 4 := rfl
      have l2 : carTrips.length = 2 := rfl
      rw [l1] at b1
      rw [l2] at b2
      have p1 := nbl_prod (ReqBridge.thrCodes Cs).length (by rw [hcl]; exact ha)
      have p2 := nbl_prod codes.length (by have := hok.hk; omega)
      have := nbl_le n hn1
      omega
    have hs := slot_le a Cs codes V hd hok h26
    have hpay : TF3Slots.paysCost a ((n + 1) ^ 26) Cs ≤ 4 * (cB * 5 ^ dB * (V + 1) ^ dB +
        (2052 * (a.coefficient + 2) ^ 2 + 40) * 1089 ^ SourceRequest.SelOrigCost.thrOE a *
          (V + 1) ^ (2 * SourceRequest.SelOrigCost.thrOE a) + 8 * V + 3) + 3 := by
      unfold TF3Slots.paysCost
      have := hs 0; have := hs 1; have := hs 2; have := hs 3
      omega
    unfold TF3Main.mCost
    omega

/-- **The THR front end on ports** (W16, `PortsE.TopFrontPort3`): the body, every `a' ≤ 4`. -/
noncomputable def topFront3 : PortsE.TopFrontPort3 a where
  x := TF3Pay.TT a + 1
  s := _
  M := TF3Port.portM a
  cost := fun V => C3 a * (V + 1) ^ D3 a
  Cc := C3 a
  Dc := D3 a
  cost_poly := fun _ => le_refl _
  run := fun Cs codes tl V hn ha hd hok => by
    obtain ⟨J, hJ, s⟩ := TF3Port.port_run a Cs codes tl V hn ha hd hok
    have hf := fuel_le a Cs codes V hn ha hd hok
    refine ⟨J, fun j => (hJ j).trans hf, s.enlarge ?_⟩
    show 2 * innerFuel a Cs codes V + 2 ≤ C3 a * (V + 1) ^ D3 a
    omega

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Cost
