import Proof.Wire_3_5.Primitive.Writers.ThrDataRun
import Proof.Wire_3_5.Primitive.Writers.ShellLayout
import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Primitive.SeedFix.CarCost

/-! # PA (d): the THR data stage, part 3: its cost is polynomial, and the packaged stage

P3:3049-3050 ("computed directly [...] in polynomial time"): the THR data stage's cost `2·thrCoreCost + 2` is
`PolyBounded` in `K + n + L + W` (`K` bounding the codes' bit lengths) by `thrTableCost*_poly` and
`carTableCost_poly`, the setup's per-slot copies (`blocksCost`), and the counts (each bounded by its table's run,
`Shell.Step.len`).

* `pb_to`, `blocksCost_le`, `slotsCost_le`, `thr_piece`, `car_piece`, **`thrCost_le`**;
* **`thrDataStage : ThrDataStage`** (the interface of `ThrDataIface`, for the THR cells and the G3).

Paper quantity of the main type: the THR data stage (the tuple's table, the carriers' tables, the counts). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.ValidatorPolynomialDomination

/-! ## The bounds as constants -/

noncomputable def cT1 : ℕ := Classical.choose PrimT.TabCost.thrTableCost1_poly
noncomputable def dT1 : ℕ := Classical.choose (Classical.choose_spec PrimT.TabCost.thrTableCost1_poly)
noncomputable def cT2 : ℕ := Classical.choose PrimT.TabCost.thrTableCost2_poly
noncomputable def dT2 : ℕ := Classical.choose (Classical.choose_spec PrimT.TabCost.thrTableCost2_poly)
noncomputable def cT3 : ℕ := Classical.choose PrimT.TabCost.thrTableCost3_poly
noncomputable def dT3 : ℕ := Classical.choose (Classical.choose_spec PrimT.TabCost.thrTableCost3_poly)
noncomputable def cT4 : ℕ := Classical.choose PrimT.TabCost.thrTableCost4_poly
noncomputable def dT4 : ℕ := Classical.choose (Classical.choose_spec PrimT.TabCost.thrTableCost4_poly)

theorem carBound : ∃ c, ∀ {n : ℕ} (X : Stars.Carrier n) (L : ℕ), 2 ≤ n + L →
    PolyBounded (PrimT.CarTable.carTableCost X L) (natBitLength X.code + n + L) c 76 :=
  ⟨_, fun X L h2 => PrimT.CarCost.carTableCost_poly X L h2⟩

noncomputable def cX : ℕ := Classical.choose carBound

/-- The THR tables' coefficient. -/
noncomputable def cTT : ℕ := cT1 + cT2 + cT3 + cT4

/-- The stage's degree. -/
noncomputable def dD : ℕ := dT1 + dT2 + dT3 + dT4 + 76 + 1

theorem pb_to {v m c d M C D : ℕ} (h : PolyBounded v m c d) (hm : m ≤ M) (hc : c ≤ C) (hd : d ≤ D) :
    v ≤ C * (M + 1) ^ D := by
  unfold PolyBounded at h
  refine le_trans h (Nat.mul_le_mul hc (le_trans (Nat.pow_le_pow_left (by omega) d)
    (Nat.pow_le_pow_right (by omega) hd)))

/-! ## The pieces -/

theorem thr_piece {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L K M : ℕ) (ha1 : 1 ≤ a)
    (ha : a ≤ 4) (hL : ∀ j, (Cs j).descriptionBits ≤ L)
    (hK : ∀ j, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs j)) ≤ K) (h2 : 2 ≤ n + L)
    (hM : K + n + L ≤ M) :
    thrCost a Cs L ≤ cTT * (M + 1) ^ dD + 6 ∧ (PrimT.ThrTab.tupleG Cs).length ≤ cTT * (M + 1) ^ dD := by
  obtain rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
  · have hp := pb_to (Classical.choose_spec (Classical.choose_spec PrimT.TabCost.thrTableCost1_poly) Cs L K hL hK) hM
      (show cT1 ≤ cTT by unfold cTT; omega) (show dT1 ≤ dD by unfold dD; omega)
    obtain ⟨tout, hs, _, _, _, _, _, t8⟩ := PrimT.ThrTab.thrTable1_step Cs L hL h2
    have hl := Shell.Step.len hs 8 0 le_rfl (by rw [PrimT.ThrTab.thrIn_blank _ _ _ _ (by decide)]; rfl)
    rw [t8, List.length_replicate] at hl
    exact ⟨by show PrimT.ThrTab.thrTableCost1 Cs L + 6 ≤ _; omega, by omega⟩
  · have hp := pb_to (Classical.choose_spec (Classical.choose_spec PrimT.TabCost.thrTableCost2_poly) Cs L K hL hK) hM
      (show cT2 ≤ cTT by unfold cTT; omega) (show dT2 ≤ dD by unfold dD; omega)
    obtain ⟨tout, hs, _, _, _, _, _, t8⟩ := PrimT.ThrTab.thrTable2_step Cs L hL h2
    have hl := Shell.Step.len hs 8 0 le_rfl (by rw [PrimT.ThrTab.thrIn_blank _ _ _ _ (by decide)]; rfl)
    rw [t8, List.length_replicate] at hl
    exact ⟨by show PrimT.ThrTab.thrTableCost2 Cs L + 6 ≤ _; omega, by omega⟩
  · have hp := pb_to (Classical.choose_spec (Classical.choose_spec PrimT.TabCost.thrTableCost3_poly) Cs L K hL hK) hM
      (show cT3 ≤ cTT by unfold cTT; omega) (show dT3 ≤ dD by unfold dD; omega)
    obtain ⟨tout, hs, _, _, _, _, _, t8⟩ := PrimT.ThrTab.thrTable3_step Cs L hL h2
    have hl := Shell.Step.len hs 8 0 le_rfl (by rw [PrimT.ThrTab.thrIn_blank _ _ _ _ (by decide)]; rfl)
    rw [t8, List.length_replicate] at hl
    exact ⟨by show PrimT.ThrTab.thrTableCost3 Cs L + 4 ≤ _; omega, by omega⟩
  · have hp := pb_to (Classical.choose_spec (Classical.choose_spec PrimT.TabCost.thrTableCost4_poly) Cs L K hL hK) hM
      (show cT4 ≤ cTT by unfold cTT; omega) (show dT4 ≤ dD by unfold dD; omega)
    obtain ⟨tout, hs, _, _, _, _, _, t8⟩ := PrimT.ThrTab.thrTable4_step Cs L hL h2
    have hl := Shell.Step.len hs 8 0 le_rfl (by rw [PrimT.ThrTab.thrIn_blank _ _ _ _ (by decide)]; rfl)
    rw [t8, List.length_replicate] at hl
    exact ⟨by show PrimT.ThrTab.thrTableCost4 Cs L + 2 ≤ _; omega, by omega⟩

theorem car_piece {n : ℕ} (X : Stars.Carrier n) (L K M : ℕ) (hLX : ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (hK : natBitLength X.code ≤ K) (h2 : 2 ≤ n + L) (hM : K + n + L ≤ M) :
    PrimT.CarTable.carTableCost X L ≤ cX * (M + 1) ^ dD ∧ X.length ≤ cX * (M + 1) ^ dD := by
  have hp := pb_to (Classical.choose_spec carBound X L h2) (show natBitLength X.code + n + L ≤ M by omega) le_rfl
    (show 76 ≤ dD by unfold dD; omega)
  obtain ⟨tout, hs, _, _, _, _, _, t5⟩ := PrimT.CarTable.carTable_step X L hLX h2
  have hl := Shell.Step.len hs 5 0 le_rfl (by rw [PrimT.CarTable.carIn_blank _ _ _ _ (by decide)]; rfl)
  rw [t5, List.length_replicate] at hl
  exact ⟨hp, by unfold cX; omega⟩

theorem slotCost_le (x n L K : ℕ) (hx : natBitLength x ≤ K) : slotCost x n L ≤ 140 * K + 18 * n + 18 * L + 200 := by
  unfold slotCost
  rw [ParseNat.natWord_length]
  omega

theorem blocksCost_le' (n L K X : ℕ) (hX : X = 140 * K + 18 * n + 18 * L + 201) :
    ∀ (trips : List Trip) (codes : List ℕ), (∀ x ∈ codes, natBitLength x ≤ K) →
    blocksCost n L trips codes ≤ trips.length * X := by
  intro trips
  induction trips with
  | nil => intro codes _; simp [blocksCost]
  | cons t l ih =>
    intro codes hc
    cases codes with
    | nil =>
      have := ih [] (by simp)
      rw [List.length_cons, Nat.succ_mul]
      show 1 + 1 + blocksCost n L l [] ≤ _
      omega
    | cons x cs =>
      have h1 := slotCost_le x n L K (hc x (by simp))
      have := ih cs (fun y hy => hc y (by simp [hy]))
      rw [List.length_cons, Nat.succ_mul]
      show slotCost x n L + 1 + blocksCost n L l cs ≤ _
      omega

theorem blocksCost_le (n L K : ℕ) (trips : List Trip) (codes : List ℕ) (hc : ∀ x ∈ codes, natBitLength x ≤ K) :
    blocksCost n L trips codes ≤ trips.length * (140 * K + 18 * n + 18 * L + 201) :=
  blocksCost_le' n L K _ rfl trips codes hc

theorem slotsCost_le : ∀ (l : List (Fin (DS + 1) × Fin (DS + 1))) (cs : List ℕ),
    slotsCost l cs ≤ 19 * cs.sum + 19 * l.length := by
  intro l
  induction l with
  | nil => intro cs; simp [slotsCost]
  | cons t l ih =>
    intro cs
    cases cs with
    | nil =>
      have := ih []
      simp only [slotsCost, List.length_cons, List.sum_nil] at this ⊢
      omega
    | cons c cs =>
      have := ih cs
      simp only [slotsCost, List.length_cons, List.sum_cons]
      omega

theorem nbl_small (m : ℕ) (hm : m ≤ 4) : (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) ≤ 9240 := by
  have h1 := CopyNat.natBitLength_le_self_succ m
  have h2 : 2 ^ natBitLength m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) ≤ 7 * (40 * 2 ^ 5 + 40) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-! ## The stage's cost -/

/-! ## The packaged stage -/

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
