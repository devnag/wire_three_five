import Proof.Wire_3_5.Primitive.Writers.ThrDataCost

/-! # PA (d): the SYM data stage's cost is polynomial

P3:3049-3050 ("computed directly [...] in polynomial time"): the SYM per-call data stage's cost
`2·Data.coreCost + 2` (the run `Data.data_step`) is `PolyBounded` in `K + n + L + W` (`K` bounding the codes' bit
lengths). The pieces are `symTableCost_poly` and `carTableCost_poly`, the setup's per-slot copies
(`ThrData.blocksCost_le`), and the counts: a carrier's size by its table's run, a circuit's bottom count by its
description bits.

* `sym_piece`, `symGates_len_le`, **`coreCost_poly`** (constants `symCc`, `symDc`).

Paper quantity of the main type: the SYM data stage's running time (the circuits' tables, the carriers' tables, the
counts). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.SupplierPipeline NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.WireExponent3_5.PrimAsm.ThrData

/-! ## The SYM bound as constants -/

noncomputable def cSy : ℕ := Classical.choose PrimT.TabCost.symTableCost_poly
noncomputable def dSy : ℕ := Classical.choose (Classical.choose_spec PrimT.TabCost.symTableCost_poly)

/-- The SYM stage's degree. -/
noncomputable def symDc : ℕ := dD + dSy

/-- The SYM stage's coefficient. -/
noncomputable def symCc : ℕ := 40 * cSy + 80 * cX + 70000

theorem pow_lift (M d e : ℕ) (h : d ≤ e) : (M + 1) ^ d ≤ (M + 1) ^ e := Nat.pow_le_pow_right (by omega) h

theorem sym_piece {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L K M : ℕ) (hL : C.descriptionBits ≤ L)
    (hK : natBitLength (encodeNormalizedSymmetricThresholdCircuit C) ≤ K) (hM : K + n + L ≤ M) :
    PrimT.SymTab.symTableCost C L ≤ cSy * (M + 1) ^ symDc :=
  pb_to (Classical.choose_spec (Classical.choose_spec PrimT.TabCost.symTableCost_poly) C L hL) (by omega) le_rfl
    (by unfold symDc dSy; omega)

theorem symGates_len_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L) :
    (Stars.symGates C).length ≤ L := by
  have := PrimT.TabCost.symDesc_pos C
  simp [Stars.symGates]
  omega

/-- **The SYM data stage's cost is polynomial** in `K + n + L + W`. -/
theorem coreCost_poly {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (L W K : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (hK : ∀ i, natBitLength (encodeNormalizedSymmetricThresholdCircuit (Cs i)) ≤ K)
    (hKX : ∀ X ∈ carriers, natBitLength X.code ≤ K) (h2 : 2 ≤ n + L) :
    PolyBounded (2 * coreCost a' Cs carriers L W + 2) (K + n + L + W) symCc symDc := by
  unfold PolyBounded
  obtain ⟨P, hP⟩ : ∃ P, P = (K + n + L + W + 1) ^ symDc := ⟨_, rfl⟩
  have hP1 : K + n + L + W + 1 ≤ P := by
    rw [hP]
    have : 1 ≤ symDc := by unfold symDc dD; omega
    calc K + n + L + W + 1 = (K + n + L + W + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) this
  rw [← hP]
  have hlift : (K + n + L + W + 1) ^ dD ≤ P := by rw [hP]; exact pow_lift _ _ _ (by unfold symDc; omega)
  -- the circuits' slots
  have hsym : ∀ i : Fin 4, symCostO L (ocOf a' Cs i) ≤ cSy * P + 2 := by
    intro i
    unfold ocOf
    by_cases hi : i.val < a'
    · rw [dif_pos hi]
      have := sym_piece (Cs ⟨i.val, hi⟩) L K (K + n + L + W) (hL _) (hK _) (by omega)
      rw [← hP] at this
      show PrimT.SymTab.symTableCost _ L + 2 ≤ _
      omega
    · rw [dif_neg hi]
      show 2 ≤ _
      omega
  -- the carriers
  have hcar : ∀ k : Fin 2, carCostO L (oxOf carriers k) ≤ cX * P + 2 := by
    intro k
    unfold oxOf
    by_cases hkl : k.val < carriers.length
    · rw [List.getElem?_eq_getElem hkl]
      have hm := List.getElem_mem hkl
      have h1 := (car_piece _ L K (K + n + L + W) (hLX _ hm) (hKX _ hm) h2 (by omega)).1
      have h3 : cX * (K + n + L + W + 1) ^ dD ≤ cX * P := Nat.mul_le_mul_left _ hlift
      show PrimT.CarTable.carTableCost _ L + 2 ≤ _
      omega
    · rw [List.getElem?_eq_none (by omega)]
      show 2 ≤ _
      omega
  have hsum : (carriers.map (·.length)).sum ≤ 2 * (cX * P) := by
    have hX : ∀ X ∈ carriers, X.length ≤ cX * P := fun X hX => by
      have h1 := (car_piece X L K (K + n + L + W) (hLX X hX) (hKX X hX) h2 (by omega)).2
      have h3 : cX * (K + n + L + W + 1) ^ dD ≤ cX * P := Nat.mul_le_mul_left _ hlift
      omega
    have : (carriers.map (·.length)).sum ≤ carriers.length * (cX * P) := by
      have := List.sum_le_card_nsmul (carriers.map (·.length)) (cX * P) (fun x hx => by
        rw [List.mem_map] at hx
        obtain ⟨X, hX', rfl⟩ := hx
        exact hX X hX')
      simpa using this
    calc _ ≤ carriers.length * (cX * P) := this
      _ ≤ 2 * (cX * P) := Nat.mul_le_mul_right _ hk
  -- the circuits' counts
  have hgs : (List.ofFn fun i => (Stars.symGates (Cs i)).length).sum ≤ 4 * L := by
    have : (List.ofFn fun i => (Stars.symGates (Cs i)).length).sum ≤
        (List.ofFn fun i => (Stars.symGates (Cs i)).length).length * L := by
      have := List.sum_le_card_nsmul (List.ofFn fun i => (Stars.symGates (Cs i)).length) L (fun x hx => by
        rw [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact symGates_len_le (Cs i) L (hL i))
      simpa using this
    rw [List.length_ofFn] at this
    calc _ ≤ a' * L := this
      _ ≤ 4 * L := Nat.mul_le_mul_right _ ha
  -- the setup
  have hcodes : ∀ x ∈ symCodes a' Cs, natBitLength x ≤ K := by
    intro x hx
    simp only [symCodes, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hK i
  have hcc : ∀ y ∈ carriers.map Stars.Carrier.code, natBitLength y ≤ K := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    exact hKX X hX
  have b1 : blocksCost n L symTrips (symCodes a' Cs) ≤ 4 * (140 * K + 18 * n + 18 * L + 201) :=
    blocksCost_le n L K symTrips (symCodes a' Cs) hcodes
  have b2 : blocksCost n L carTrips (carriers.map Stars.Carrier.code) ≤ 2 * (140 * K + 18 * n + 18 * L + 201) :=
    blocksCost_le n L K carTrips (carriers.map Stars.Carrier.code) hcc
  have hlenc : (symCodes a' Cs).length ≤ 4 := by simp [symCodes]; omega
  have hlencc : (carriers.map Stars.Carrier.code).length ≤ 4 := by simp; omega
  have s1 := nbl_small _ hlenc
  have s2 := nbl_small _ hlencc
  have hnb := CopyNat.natBitLength_le_self_succ n
  have hsetup : setupCost n L (symCodes a' Cs) (carriers.map Stars.Carrier.code) ≤ 30000 * P := by
    unfold setupCost
    omega
  -- the collection
  have hcol := slotsCost_le carC (carriers.map (·.length))
  have hcolS := slotsCost_le symC (List.ofFn fun i => (Stars.symGates (Cs i)).length)
  rw [show carC.length = 2 from rfl] at hcol
  rw [show symC.length = 4 from rfl] at hcolS
  -- the tables
  have t0 := hsym 0
  have t1 := hsym 1
  have t2 := hsym 2
  have t3 := hsym 3
  have h0 := hcar 0
  have h1 := hcar 1
  unfold coreCost tabsCost collectCost
  have e : (40 * cSy + 80 * cX + 70000) * P = 40 * (cSy * P) + 80 * (cX * P) + 70000 * P := by ring
  unfold symCc
  rw [e]
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.Data
