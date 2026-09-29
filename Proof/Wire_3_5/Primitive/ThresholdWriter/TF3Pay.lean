import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Main
import Proof.Wire_3_5.Primitive.ThresholdWriter.PayM

/-! # TopFrontPort3 body, part 4: the payload machines docked on the filled slots (`payI`, `pays_step`)

P3:2543-2551 (row:threshold-rows): each circuit's retained top is decomposed by the algorithm, and its children are
the payload `payOf alg c` (`TopFront.payOf`); P3:3071-3091: circuit `i` of the call is decoded from its code. The word
stage (`TF3Main`) leaves each filled slot `i` in the decode-block entry form on its streams `0 … 1780`; the payload
machine `PayM.payM` (the decode block, then base's `SourceTopNative`) runs there, with its top machine's own tapes in
a fresh region (the top machine's tape count depends on the algorithm, so it lives outside the word layout):

* the layout `TT a = (DS + 2 + DR) + 4·(T_a − 1)` (`dT` the word machine's tapes, `xT` the four top regions),
  `payMap a i` (slot `i`'s dock), `payMap_inj`, `payMap_ne` (the slots' images are disjoint and miss the low streams);
* `payDock`, `payI` (a `Block.branchM` on the slot's first cell), **`pay_dock`**, **`payI_filled`**, **`payI_blank`**.

Paper quantities of the main type: one circuit's retained-top children (`payOf`) and native word (`thrWord`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Pay
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data

variable (a : DecompositionAlgorithm)

/-- The word machine's tapes. -/
abbrev Dt : ℕ := DS + 2 + DR
/-- The four top regions. -/
abbrev X : ℕ := 4 * (PayM.Ta a - 1)
/-- **The front end's inner layout.** -/
abbrev TT : ℕ := Dt + X a

def dT (j : Fin Dt) : Fin (TT a) := Fin.castAdd (X a) j
def xT (k : Fin (X a)) : Fin (TT a) := Fin.natAdd Dt k

theorem dT_val (j : Fin Dt) : (dT a j).val = j.val := rfl
theorem xT_val (k : Fin (X a)) : (xT a k).val = Dt + k.val := rfl

/-- Slot `i`'s top region, tape `k`. -/
def topT (i : Fin 4) (k : Fin (PayM.Ta a - 1)) : Fin (X a) :=
  ⟨(PayM.Ta a - 1) * i.val + k.val, by
    have hi := i.isLt; have hk := k.isLt
    have h1 : (PayM.Ta a - 1) * i.val + k.val < (PayM.Ta a - 1) * (i.val + 1) := by rw [Nat.mul_succ]; omega
    have h2 : (PayM.Ta a - 1) * (i.val + 1) ≤ (PayM.Ta a - 1) * 4 := Nat.mul_le_mul_left _ (by omega)
    show (PayM.Ta a - 1) * i.val + k.val < 4 * (PayM.Ta a - 1)
    omega⟩

/-- **Slot `i`'s dock**: the payload machine's block tapes on the slot's streams `0 … 1780`, its top tapes on the
slot's region. -/
def payMap (i : Fin 4) (k : Fin (PayM.PT a)) : Fin (TT a) :=
  if h : k.val < 1781 then dT a (sTape (nr := DR) (sSym i ⟨k.val, by omega⟩))
  else xT a (topT a i ⟨k.val - 1781, by have := k.isLt; unfold PayM.PT at this; omega⟩)

theorem payMap_lo (i : Fin 4) (k : Fin (PayM.PT a)) (h : k.val < 1781) :
    (payMap a i k).val = 14 + 1789 * i.val + k.val + 1 := by
  unfold payMap
  rw [dif_pos h, dT_val, DockW.sTape_val, sSym_val]
  simp

theorem payMap_hi (i : Fin 4) (k : Fin (PayM.PT a)) (h : ¬ k.val < 1781) :
    (payMap a i k).val = Dt + ((PayM.Ta a - 1) * i.val + (k.val - 1781)) := by
  unfold payMap
  rw [dif_neg h, xT_val]
  rfl

theorem payMap_inj (i : Fin 4) : Function.Injective (payMap a i) := by
  intro k k' e
  have hv := congrArg Fin.val e
  apply Fin.ext
  by_cases h : k.val < 1781 <;> by_cases h' : k'.val < 1781
  · rw [payMap_lo a i k h, payMap_lo a i k' h'] at hv; omega
  · rw [payMap_lo a i k h, payMap_hi a i k' h'] at hv; unfold Dt DS at hv; have := i.isLt; omega
  · rw [payMap_hi a i k h, payMap_lo a i k' h'] at hv; unfold Dt DS at hv; have := i.isLt; omega
  · rw [payMap_hi a i k h, payMap_hi a i k' h'] at hv; omega

/-- Two slots' docks never meet. -/
theorem payMap_disj (i i' : Fin 4) (hii : i ≠ i') (k k' : Fin (PayM.PT a)) : payMap a i k ≠ payMap a i' k' := by
  intro e
  have hv := congrArg Fin.val e
  have hk := k.isLt
  have hk' := k'.isLt
  unfold PayM.PT at hk hk'
  have hne : i.val ≠ i'.val := fun h => hii (Fin.ext h)
  by_cases h : k.val < 1781 <;> by_cases h' : k'.val < 1781
  · rw [payMap_lo a i k h, payMap_lo a i' k' h'] at hv; omega
  · rw [payMap_lo a i k h, payMap_hi a i' k' h'] at hv; unfold Dt DS at hv; have := i.isLt; omega
  · rw [payMap_hi a i k h, payMap_lo a i' k' h'] at hv; unfold Dt DS at hv; have := i'.isLt; omega
  · rw [payMap_hi a i k h, payMap_hi a i' k' h'] at hv
    have e1 : (PayM.Ta a - 1) * i.val + (k.val - 1781) < (PayM.Ta a - 1) * (i.val + 1) := by
      rw [Nat.mul_succ]; omega
    have e2 : (PayM.Ta a - 1) * i'.val + (k'.val - 1781) < (PayM.Ta a - 1) * (i'.val + 1) := by
      rw [Nat.mul_succ]; omega
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : (PayM.Ta a - 1) * (i.val + 1) ≤ (PayM.Ta a - 1) * i'.val := Nat.mul_le_mul_left _ (by omega)
      omega
    · have : (PayM.Ta a - 1) * (i'.val + 1) ≤ (PayM.Ta a - 1) * i.val := Nat.mul_le_mul_left _ (by omega)
      omega

/-- A slot's dock misses every word stream below `14` (the request, the count, the prepared streams). -/
theorem payMap_ne_low (i : Fin 4) (k : Fin (PayM.PT a)) (s : Fin (DS + 1)) (hs : s.val < 14) :
    payMap a i k ≠ dT a (sTape (nr := DR) s) := by
  intro e
  have hv := congrArg Fin.val e
  rw [dT_val, DockW.sTape_val] at hv
  by_cases h : k.val < 1781
  · rw [payMap_lo a i k h] at hv; split_ifs at hv <;> omega
  · rw [payMap_hi a i k h] at hv; unfold Dt DS at hv; split_ifs at hv <;> omega

/-- **Slot `i`'s payload machine, docked.** -/
noncomputable def payDock (i : Fin 4) := RecoveryFocus.machine (payMap a i) (PayM.payM a)

/-- **Slot `i`'s stage**: the payload machine when the slot is filled (its first cell reads `1`), else nothing. -/
noncomputable def payI (i : Fin 4) :=
  Block.branchM (dT a (sTape (nr := DR) (sSym i 0))) (payDock a i) (Block.idle (TT a))

theorem payMap_zero (i : Fin 4) : payMap a i ⟨0, by unfold PayM.PT; omega⟩ = dT a (sTape (nr := DR) (sSym i 0)) := by
  unfold payMap; rw [dif_pos (by norm_num)]; rfl

/-- **The docked payload machine**: at a bank whose slot-`i` dock holds the payload machine's entry at heads `0`. -/
theorem pay_dock (i : Fin 4) {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ) (hL : c.descriptionBits ≤ L)
    (H : Fin (TT a) → ℕ) (A : Fin (TT a) → List Bool) (hH : ∀ k, H (payMap a i k) = 0)
    (hA : ∀ k, A (payMap a i k) = PayM.payIn a (encodeNormalizedThresholdThresholdCircuit c) n L k) :
    ∃ out : Fin (PayM.PT a) → List Bool,
      Step (payDock a i) (ThrTab.thrBlockCost c L + 1 + PayM.topBudget a c) H A (dockH (payMap a i) H (fun _ => 0))
        (install (payMap a i) A out) ∧
      out (PayM.outTop a) = TopFront.payOf a c ∧
      out ⟨1692, by show 1692 < 1781 + (PayM.Ta a - 1); omega⟩ = PCJd4d1d9d7d1fa4313_Production.thrWord c := by
  obtain ⟨out, s, h1, h2, -, -, -⟩ := PayM.pay_step a c L hL
  exact ⟨out, s.dock (payMap a i) (payMap_inj a i) H A hH hA, h1, h2⟩

/-- **A filled slot**: the payload machine runs; outside the slot's dock nothing changes. -/
theorem payI_filled (i : Fin 4) {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (hL : c.descriptionBits ≤ L) (H : Fin (TT a) → ℕ) (A : Fin (TT a) → List Bool) (hH : ∀ k, H (payMap a i k) = 0)
    (hA : ∀ k, A (payMap a i k) = PayM.payIn a (encodeNormalizedThresholdThresholdCircuit c) n L k) :
    ∃ (H' : Fin (TT a) → ℕ) (A' : Fin (TT a) → List Bool),
      Step (payI a i) (ThrTab.thrBlockCost c L + 1 + PayM.topBudget a c + 2) H A H' A' ∧
      (∀ t, (∀ k, payMap a i k ≠ t) → H' t = H t ∧ A' t = A t) ∧ (∀ k, H' (payMap a i k) = 0) ∧
      A' (payMap a i (PayM.outTop a)) = TopFront.payOf a c ∧
      A' (payMap a i ⟨1692, by show 1692 < 1781 + (PayM.Ta a - 1); omega⟩) =
        PCJd4d1d9d7d1fa4313_Production.thrWord c := by
  obtain ⟨out, s, h1, h2⟩ := pay_dock a i c L hL H A hH hA
  have hb : readTapeBit (A (dT a (sTape (nr := DR) (sSym i 0)))) (H (dT a (sTape (nr := DR) (sSym i 0)))) = true := by
    rw [← payMap_zero, hA, hH]
    unfold PayM.payIn
    rw [dif_pos (by norm_num)]
    exact frame_natWord_head _
  refine ⟨_, _, Block.branch_true _ _ s hb, fun t ht => ⟨dockH_other _ _ _ _ ht, install_other _ _ _ _ ht⟩,
    fun k => by simp [payMap_inj a i], ?_, ?_⟩
  · rw [install_slot _ (payMap_inj a i)]; exact h1
  · rw [install_slot _ (payMap_inj a i)]; exact h2

/-- **An empty slot**: nothing changes. -/
theorem payI_blank (i : Fin 4) (H : Fin (TT a) → ℕ) (A : Fin (TT a) → List Bool)
    (hb : A (dT a (sTape (nr := DR) (sSym i 0))) = []) :
    Step (payI a i) 2 H A H A := by
  have := Block.branch_false (dT a (sTape (nr := DR) (sSym i 0))) (payDock a i)
    (ListMachine.Print.idle_step H A) (by rw [hb]; rfl)
  exact this.enlarge (by omega)

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Pay
