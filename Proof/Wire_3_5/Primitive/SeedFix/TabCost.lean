import Proof.Rows.RowsSymBounds
import Proof.SourceAssembly.SourceRequestSelOrigCost
import Proof.Wire_3_5.Primitive.SeedFix.TabThr

/-! # The gate tables: polynomial fuel (P3:3049-3050, 1648-1650)

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050); "evaluating at most
`n` coordinate functions and adding polynomial-bit integers takes polynomial time" (P3:1648-1650). This module proves
that the SYM gate table machine runs in polynomial time in its input size. The form is base's `PolyBounded fuel
measure c d` (`fuel ≤ c·(measure + 1)^d`, `ValidatorPolynomialDomination`), with the measure `k + n + L`: the code's
bit length `k`, the arity `n`, and the description bound `L`.

The pieces are base's bounds:
* the preparation is linear;
* base's polynomial capacity run (`BlockUnaryCalc.poly_cost_polyBounded`);
* base's decoder chain (`SelOrigCost.wFuel_le`, quadratic in the capacity `10^30·(k+2)^26`);
* the native word (`Admission.symWord_le`);
* the scan and the writer, polynomial in the table width `h ≤ |symWord|`.

Paper quantity of the main type (**`symTableCost_poly`**): the SYM table's running time is polynomial. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.TabCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires.WireExponent3_5.PrimT.ThrTab
open PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.SymBounds (J pb_sq)

/-! ## Shared pieces -/

/-- The preparation. -/
theorem prep_pb (k n L m : ℕ) (hm : k + n + L ≤ m) : PolyBounded (2 * prepCost k n L + 2) m 122 1 := by
  unfold PolyBounded prepCost; rw [pow_one]; omega

/-- Base's capacity run at `k + 1 ≤ m`. -/
theorem power_pb (k m : ℕ) (hm : k + 1 ≤ m) :
    PolyBounded (PCPSerializerCapacity.Power.budget 26 cC (k + 1)) m
      (BlockPlatform.UnaryCalc.polyCoefficient 26 cC) 27 :=
  (BlockPlatform.UnaryCalc.poly_cost_polyBounded 26 cC (k + 1)).measure_mono hm

/-- Base's decoder chain's fuel at the capacity `10^30·(k+2)^26`. -/
theorem wFuel_pb (k n m : ℕ) (bits : List Bool) (hb : bits.length = k) (hkm : k + 1 ≤ m) (hnm : n ≤ m) :
    PolyBounded (SourceRequest.ThrOriginal.wFuel (cC * (k + 1 + 1) ^ 26) n bits) m
      (6002 * ((cC + 3) * (cC + 3))) (0 + (26 + 26)) := by
  set S := cC * (k + 1 + 1) ^ 26 + n + k with hS
  have hw := SourceRequest.SelOrigCost.wFuel_le (cC * (k + 1 + 1) ^ 26) n k S (by omega) (by omega) (by omega)
  have hS1 : PolyBounded (S + 1) m (cC + 3) 26 := by
    unfold PolyBounded
    have hp : (k + 1 + 1) ^ 26 ≤ (m + 1) ^ 26 := Nat.pow_le_pow_left (by omega) _
    have h1 : m + 1 ≤ (m + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    have h2 : cC * (k + 1 + 1) ^ 26 ≤ cC * (m + 1) ^ 26 := Nat.mul_le_mul_left _ hp
    rw [Nat.add_mul]; omega
  have hconst := (BlockPlatform.PolyBound.const 6002 m 0).mul (pb_sq hS1)
  refine hconst.mono ?_
  have e : SourceRequest.ThrOriginal.wFuel (cC * (k + 1 + 1) ^ 26) n bits =
      1 + 1 + CloseoutRowsSupportStream.circuitBudget (cC * (k + 1 + 1) ^ 26) n k := by
    unfold SourceRequest.ThrOriginal.wFuel; rw [hb]
  rw [e]; exact hw

/-- The table writer's fuel at width `h`, arity `n`, and `g ≤ h` gates. -/
theorem tab_pb (n h g m ch : ℕ) (hn : n ≤ m) (hh : PolyBounded h m ch 2) (hg : g ≤ h) :
    PolyBounded (2 * tabCost n h g + 2) m (2 * (10 * ch + 13 + ch * (203 * ch + 213)) + 2) 5 := by
  unfold PolyBounded at hh ⊢
  set M := m + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have p23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by norm_num)
  have p35 : M ^ 3 ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by norm_num)
  have p13 : M ≤ M ^ 3 := by have := Nat.pow_le_pow_right hM1 (show 1 ≤ 3 by norm_num); simpa using this
  have hnh : n * h ≤ ch * M ^ 3 := by
    calc n * h ≤ M * (ch * M ^ 2) := Nat.mul_le_mul (by omega) hh
      _ = ch * M ^ 3 := by ring
  have hgate : gateCost n h + 2 ≤ (203 * ch + 213) * M ^ 3 := by
    unfold gateCost gateACost gateBCost
    have e1 : 16 * n * h = 16 * (n * h) := by ring
    have e2 : 70 * n * h = 70 * (n * h) := by ring
    rw [e1, e2]
    have hn3 : n ≤ M ^ 3 := by omega
    have hh3 : h ≤ ch * M ^ 3 := hh.trans (Nat.mul_le_mul_left _ p23)
    have h13 : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
    have e3 : (203 * ch + 213) * M ^ 3 = 203 * (ch * M ^ 3) + 213 * M ^ 3 := by ring
    rw [e3]; omega
  have hprod : g * (gateCost n h + 2) ≤ ch * (203 * ch + 213) * M ^ 5 := by
    calc g * (gateCost n h + 2) ≤ (ch * M ^ 2) * ((203 * ch + 213) * M ^ 3) := Nat.mul_le_mul (hg.trans hh) hgate
      _ = ch * (203 * ch + 213) * M ^ 5 := by ring
  have hh5 : h ≤ ch * M ^ 5 := hh.trans (Nat.mul_le_mul_left _ (p23.trans p35))
  have h15 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ (by omega)
  unfold tabCost
  have e4 : (2 * (10 * ch + 13 + ch * (203 * ch + 213)) + 2) * M ^ 5 =
      2 * (10 * (ch * M ^ 5)) + 2 * 13 * M ^ 5 + 2 * (ch * (203 * ch + 213) * M ^ 5) + 2 * M ^ 5 := by ring
  rw [e4]; omega

/-- The number of gates is at most the table width. -/
theorem length_le_tabH {n : ℕ} (G : List (NormalizedThresholdGate n)) : G.length ≤ tabH G := by
  induction G with
  | nil => simp [tabH, tabSeg]
  | cons g G ih => simp only [tabH, tabSeg_cons, List.length_append, frame_length, List.length_cons] at ih ⊢; omega

/-! ## The SYM table -/

/-- The SYM table width is at most its native word. -/
theorem tabH_sym_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) :
    tabH (Stars.symGates C) ≤ (symWord C).length := by
  rw [symWord_eq]; simp only [List.length_append, tabH]; omega

theorem symDesc_pos {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) : C.bottomCount + 1 ≤ C.descriptionBits := by
  unfold NormalizedSymmetricThresholdCircuit.descriptionBits; omega

/-- **The SYM table's fuel is polynomial** in the code's bit length, the arity and the description bound. -/
theorem symTableCost_poly : ∃ c d, ∀ {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ),
    C.descriptionBits ≤ L →
    PolyBounded (symTableCost C L) (natBitLength (encodeNormalizedSymmetricThresholdCircuit C) + n + L) c d := by
  exact ⟨_, _, fun {n} C L hL => by
  set k := natBitLength (encodeNormalizedSymmetricThresholdCircuit C) with hk
  set m := k + n + L with hm
  have hd := symDesc_pos C
  have hkm : k + 1 ≤ m := by omega
  have hnm : n ≤ m := by omega
  have hsw : PolyBounded (symWord C).length m 27 2 := by
    unfold PolyBounded
    have h1 := Admission.symWord_le C
    have h2 : (4 * n + 23) * (C.descriptionBits + 1) ≤ (27 * (m + 1)) * (m + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : 27 * (m + 1) * (m + 1) = 27 * (m + 1) ^ 2 := by ring
    omega
  have hh : PolyBounded (tabH (Stars.symGates C)) m 27 2 := hsw.mono (tabH_sym_le C)
  have hg := length_le_tabH (Stars.symGates C)
  have hA := prep_pb k n L m (le_refl _)
  have hB := power_pb k m hkm
  have hW := wFuel_pb k n m (binary k (encodeNormalizedSymmetricThresholdCircuit C)) (binary_length _ _) hkm hnm
  have hD := BlockPlatform.PolyBound.add (BlockPlatform.PolyBound.add
    ((BlockPlatform.PolyBound.const 2 m 0).mul hW) ((BlockPlatform.PolyBound.const 4 m 0).mul hsw))
    (BlockPlatform.PolyBound.const 7 m 0)
  have hE : PolyBounded (2 * (scanCost C.bottomCount (List.ofFn C.top) (tabH (Stars.symGates C)) + 4) + 2) m
      (2 * (17 + 42 * 27 + 16) + 2) 2 := by
    unfold PolyBounded scanCost at *
    have hnb := PolynomialClock.natBitLength_le_succ C.bottomCount
    have h1 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [List.length_ofFn]
    have e : (2 * (17 + 42 * 27 + 16) + 2) * (m + 1) ^ 2 =
        2 * (17 * (m + 1) ^ 2 + 42 * (27 * (m + 1) ^ 2) + 16 * (m + 1) ^ 2) + 2 * (m + 1) ^ 2 := by ring
    rw [e]; omega
  have hF := tab_pb n (tabH (Stars.symGates C)) (Stars.symGates C).length m 27 hnm hh hg
  have tot := J (BlockPlatform.PolyBound.const 1 m 0) (J hA (J hB (J hD (J hE hF))))
  unfold symTableCost
  exact tot⟩

/-! ## The THR tables -/

theorem thrDesc_pos {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) : C.bottomCount + 1 ≤ C.descriptionBits := by
  have e : C.descriptionBits = C.top.gate.encodingBits + C.bottomCount + ∑ i, (C.bottom i).descriptionBits := rfl
  have h1 : 1 ≤ C.top.gate.encodingBits := by
    unfold NormalizedThresholdGate.encodingBits intBitLength; omega
  omega

/-- A THR circuit's native word, at description `≤ L` and arity `n`, in any measure `m ≥ n + L`. -/
theorem thrWord_pb {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (L m : ℕ) (hL : C.descriptionBits ≤ L)
    (hm : n + L ≤ m) : PolyBounded (thrWord C).length m 68 2 := by
  unfold PolyBounded
  have h1 := Admission.thrWord_le C
  have h2 : (4 * n + 4 * C.descriptionBits + 60) * (C.descriptionBits + 1) ≤ (68 * (m + 1)) * (m + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 68 * (m + 1) * (m + 1) = 68 * (m + 1) ^ 2 := by ring
  omega

/-- **One THR decode block's fuel is polynomial.** -/
theorem thrBlock_poly : ∃ c d, ∀ {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) (L K : ℕ),
    C.descriptionBits ≤ L → natBitLength (encodeNormalizedThresholdThresholdCircuit C) ≤ K →
    PolyBounded (thrBlockCost C L) (K + n + L) c d := by
  exact ⟨_, _, fun {n} C L K hL hK => by
  set k := natBitLength (encodeNormalizedThresholdThresholdCircuit C) with hk
  set m := K + n + L with hm
  have hd := thrDesc_pos C
  have hkm : k + 1 ≤ m := by omega
  have hA := prep_pb k n L m (by omega)
  have hB := power_pb k m hkm
  have hW := wFuel_pb k n m (binary k (encodeNormalizedThresholdThresholdCircuit C)) (binary_length _ _) hkm (by omega)
  have hD := BlockPlatform.PolyBound.add (BlockPlatform.PolyBound.add
    ((BlockPlatform.PolyBound.const 2 m 0).mul hW) ((BlockPlatform.PolyBound.const 4 m 0).mul
      (thrWord_pb C L m hL (by omega)))) (BlockPlatform.PolyBound.const 7 m 0)
  have tot := J hA (J hB hD)
  unfold thrBlockCost
  exact tot⟩

/-- A THR circuit's native word bounds its table width, its top word and its top wire count. -/
theorem thrWord_parts {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    tabH ((SupplierEstimator.thresholdCircuitOccurrences C).map (·.gate)) ≤ (thrWord C).length ∧
      (thresholdWord (CompilerSemantics.nonStrictAsStrict (retainedTopGate C))).length ≤ (thrWord C).length ∧
      C.top.wireCount ≤ C.descriptionBits := by
  have hw := thrWord_eq C
  have hc : C.top.wireCount ≤ C.bottomCount := by
    unfold SupportedNormalizedGate.wireCount
    have := Finset.card_le_univ C.top.support
    simpa using this
  have hd := thrDesc_pos C
  refine ⟨?_, ?_, by omega⟩
  · rw [hw]; simp only [List.length_append, tabH]; omega
  · rw [hw]; simp only [List.length_append, frame_length]; omega

theorem scanCosts_le {ns n : ℕ} (B : ℕ) : ∀ (its : List (ScanItem ns n)),
    (∀ it ∈ its, scanCost it.x it.y (tabH it.G) + 1 ≤ B) → scanCosts its ≤ its.length * B
  | [], _ => by simp [scanCosts]
  | it :: its, h => by
    have h1 := h it (by simp)
    have h2 := scanCosts_le B its (fun it' hit => h it' (by simp [hit]))
    simp only [scanCosts, List.length_cons, Nat.succ_mul]; omega

theorem tabH_flatten {n : ℕ} : ∀ (LL : List (List (NormalizedThresholdGate n))),
    tabH LL.flatten = (LL.map tabH).sum
  | [] => by simp [tabH, tabSeg]
  | G :: LL => by
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    rw [← tabH_flatten LL]; unfold tabH; rw [tabSeg_append, List.length_append]

/-- **The THR tail** (the scan and the table writer) at `a ≤ 4` circuits. -/
theorem thrTail_poly : ∃ c d, ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L m : ℕ),
    (∀ j, (Cs j).descriptionBits ≤ L) → n + L ≤ m →
    PolyBounded (thrScanCost ha Cs + 1 + (2 * tabCost n (tabH (tupleG Cs)) (tupleG Cs).length + 2)) m c d := by
  exact ⟨_, _, fun {n a} ha Cs L m hL hm => by
  have hw : ∀ j, PolyBounded (thrWord (Cs j)).length m 68 2 := fun j => thrWord_pb (Cs j) L m (hL j) hm
  have hh : PolyBounded (tabH (tupleG Cs)) m (4 * 68) 2 := by
    unfold PolyBounded
    set GG := List.ofFn fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate) with hGG
    have e : tabH (tupleG Cs) = (GG.map tabH).sum := tabH_flatten GG
    have hsum : (GG.map tabH).sum ≤ (GG.map tabH).length • (68 * (m + 1) ^ 2) := by
      apply List.sum_le_card_nsmul
      intro x hx
      obtain ⟨G', hG', rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hG'
      exact (thrWord_parts (Cs j)).1.trans (hw j)
    rw [smul_eq_mul, List.length_map, hGG, List.length_ofFn] at hsum
    have ha' : a * (68 * (m + 1) ^ 2) ≤ 4 * (68 * (m + 1) ^ 2) := Nat.mul_le_mul_right _ ha
    rw [e]
    have e2 : 4 * 68 * (m + 1) ^ 2 = 4 * (68 * (m + 1) ^ 2) := by ring
    rw [e2]; exact hsum.trans ha'
  have hg := length_le_tabH (tupleG Cs)
  have hF := tab_pb n (tabH (tupleG Cs)) (tupleG Cs).length m (4 * 68) (by omega) hh hg
  have hS : PolyBounded (thrScanCost ha Cs) m (2 * (3 + 1 + 4 * (24 + 47 * 68 + 1)) + 2) 2 := by
    unfold PolyBounded thrScanCost
    have hsc := scanCosts_le ((24 + 47 * 68 + 1) * (m + 1) ^ 2)
      (List.ofFn fun j : Fin a => scanItem (Cs j) ⟨j.val, by omega⟩) (by
        intro it hit
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hit
        obtain ⟨p1, p2, p3⟩ := thrWord_parts (Cs j)
        have hwj := hw j
        unfold PolyBounded at hwj
        have hnb := PolynomialClock.natBitLength_le_succ (Cs j).top.wireCount
        have hLj := hL j
        have h1 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        have h2 : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        simp only [scanItem, scanCost]
        have e : (24 + 47 * 68 + 1) * (m + 1) ^ 2 = 24 * (m + 1) ^ 2 + 47 * (68 * (m + 1) ^ 2) + (m + 1) ^ 2 := by ring
        rw [e]; omega)
    rw [List.length_ofFn] at hsc
    have h1 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : a * ((24 + 47 * 68 + 1) * (m + 1) ^ 2) ≤ 4 * ((24 + 47 * 68 + 1) * (m + 1) ^ 2) :=
      Nat.mul_le_mul_right _ ha
    have e : (2 * (3 + 1 + 4 * (24 + 47 * 68 + 1)) + 2) * (m + 1) ^ 2 =
        2 * (4 * (m + 1) ^ 2) + 2 * (4 * ((24 + 47 * 68 + 1) * (m + 1) ^ 2)) + 2 * (m + 1) ^ 2 := by ring
    rw [e]; omega
  exact J hS hF⟩

theorem thrTableCost1_poly : ∃ c d, ∀ {n : ℕ} (Cs : Fin 1 → NormalizedThresholdThresholdCircuit n) (L K : ℕ),
    (∀ j, (Cs j).descriptionBits ≤ L) → (∀ j, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs j)) ≤ K) →
    PolyBounded (thrTableCost1 Cs L) (K + n + L) c d := by
  obtain ⟨cb, db, hb⟩ := thrBlock_poly
  obtain ⟨ct, dt, ht⟩ := thrTail_poly
  exact ⟨_, _, fun {n} Cs L K hL hK => by
    have tot := J (BlockPlatform.PolyBound.const 1 (K + n + L) 0) (J (hb (Cs 0) L K (hL 0) (hK 0))
      (ht (show 1 ≤ 4 by decide) Cs L (K + n + L) hL (by omega)))
    unfold thrTableCost1
    exact tot⟩

theorem thrTableCost2_poly : ∃ c d, ∀ {n : ℕ} (Cs : Fin 2 → NormalizedThresholdThresholdCircuit n) (L K : ℕ),
    (∀ j, (Cs j).descriptionBits ≤ L) → (∀ j, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs j)) ≤ K) →
    PolyBounded (thrTableCost2 Cs L) (K + n + L) c d := by
  obtain ⟨cb, db, hb⟩ := thrBlock_poly
  obtain ⟨ct, dt, ht⟩ := thrTail_poly
  exact ⟨_, _, fun {n} Cs L K hL hK => by
    have tot := J (BlockPlatform.PolyBound.const 1 (K + n + L) 0) (J (hb (Cs 0) L K (hL 0) (hK 0))
      (J (hb (Cs 1) L K (hL 1) (hK 1)) (ht (show 2 ≤ 4 by decide) Cs L (K + n + L) hL (by omega))))
    unfold thrTableCost2
    exact tot⟩

theorem thrTableCost3_poly : ∃ c d, ∀ {n : ℕ} (Cs : Fin 3 → NormalizedThresholdThresholdCircuit n) (L K : ℕ),
    (∀ j, (Cs j).descriptionBits ≤ L) → (∀ j, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs j)) ≤ K) →
    PolyBounded (thrTableCost3 Cs L) (K + n + L) c d := by
  obtain ⟨cb, db, hb⟩ := thrBlock_poly
  obtain ⟨ct, dt, ht⟩ := thrTail_poly
  exact ⟨_, _, fun {n} Cs L K hL hK => by
    have tot := J (BlockPlatform.PolyBound.const 1 (K + n + L) 0) (J (hb (Cs 0) L K (hL 0) (hK 0))
      (J (hb (Cs 1) L K (hL 1) (hK 1)) (J (hb (Cs 2) L K (hL 2) (hK 2))
        (ht (show 3 ≤ 4 by decide) Cs L (K + n + L) hL (by omega)))))
    unfold thrTableCost3
    exact tot⟩

theorem thrTableCost4_poly : ∃ c d, ∀ {n : ℕ} (Cs : Fin 4 → NormalizedThresholdThresholdCircuit n) (L K : ℕ),
    (∀ j, (Cs j).descriptionBits ≤ L) → (∀ j, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs j)) ≤ K) →
    PolyBounded (thrTableCost4 Cs L) (K + n + L) c d := by
  obtain ⟨cb, db, hb⟩ := thrBlock_poly
  obtain ⟨ct, dt, ht⟩ := thrTail_poly
  exact ⟨_, _, fun {n} Cs L K hL hK => by
    have tot := J (BlockPlatform.PolyBound.const 1 (K + n + L) 0) (J (hb (Cs 0) L K (hL 0) (hK 0))
      (J (hb (Cs 1) L K (hL 1) (hK 1)) (J (hb (Cs 2) L K (hL 2) (hK 2)) (J (hb (Cs 3) L K (hL 3) (hK 3))
        (ht (show 4 ≤ 4 by decide) Cs L (K + n + L) hL (by omega))))))
    unfold thrTableCost4
    exact tot⟩

end NearCubicWires.WireExponent3_5.PrimT.TabCost
