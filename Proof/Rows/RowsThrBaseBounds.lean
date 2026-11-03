import Proof.Rows.RowsThrBounds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrBaseBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open RowsConstruction.SymBounds RowsConstruction.ThrBounds
noncomputable section

/-! ## 1. Budget polynomials of the magnitude/base workers -/

theorem uni_pb : ∃ c d, ∀ m w C : Nat, w ≤ m → C ≤ m →
    PolyBounded (CloseoutRowsPoolMinimum.uniformBudget w C) m c d :=
  ⟨_, _, fun m _ _ hw hC =>
    PolyBound.add (PolyBound.add ((const 28 m 0).mul (pb_var hw)) ((const 2 m 0).mul (pb_var hC))) (const 47 m 0)⟩

theorem slb_pb : ∃ c d, ∀ (m : Nat) (xs : List CloseoutRowsPoolWeight.Item) (w C : Nat), xs.length ≤ m → w ≤ m →
    C ≤ m → PolyBounded (C10NaturalHardwireScore.loopBudget xs w C) m c d := by
  obtain ⟨c0, d0, h0⟩ := uni_pb
  exact ⟨_, _, fun m _ w C hx hw hC =>
    PolyBound.add ((pb_var hx).mul (PolyBound.add (h0 m w C hw hC) (const 3 m 0))) (const 3 m 0)⟩

theorem plb_pb : ∃ c d, ∀ (m : Nat) (xs : List CloseoutRowsPoolWeight.Item) (w C : Nat), xs.length ≤ m → w ≤ m →
    C ≤ m → PolyBounded (CloseoutRowsPoolMinimum.loopBudget xs w C) m c d := by
  obtain ⟨c0, d0, h0⟩ := uni_pb
  exact ⟨_, _, fun m _ w C hx hw hC =>
    PolyBound.add ((pb_var hx).mul (PolyBound.add (h0 m w C hw hC) (const 3 m 0))) (const 3 m 0)⟩

theorem items_length {n : Nat} (g : ExactThresholdGate n) : (C10ThresholdChildMagnitude.items g).length = n+1 := by
  simp [C10ThresholdChildMagnitude.items, C10ThresholdChildMagnitude.fields]

theorem cm_pb : ∃ c d, ∀ (m n : Nat) (g : ExactThresholdGate n) (w C : Nat), n+1 ≤ m → w ≤ m → C ≤ m →
    PolyBounded (C10ThresholdChildMagnitude.budget g w C) m c d := by
  obtain ⟨c0, d0, h0⟩ := slb_pb
  obtain ⟨c1, d1, h1⟩ := plb_pb
  exact ⟨_, _, fun m n g w C hn hw hC =>
    have hx : (C10ThresholdChildMagnitude.items g).length ≤ m := by rw [items_length]; exact hn
    PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      ((const 2 m 0).mul (h0 m _ w C hx hw hC)) (const 2 m 0)) (const 1 m 0)) (h1 m _ w C hx hw hC))
      ((const 12 m 0).mul (pb_var hw))) (const 14 m 0)⟩

theorem sbr_pb : ∃ c d, ∀ (m n : Nat) (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C U : Nat),
    n+1 ≤ m → gs.length ≤ m → ((gs.take i.val).flatMap exactWord).length ≤ m → i.val ≤ m →
    (exactWord (gs.get i)).length ≤ m → w ≤ m → C ≤ m → U ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_SelectedBaseRun.budget gs i w C U) m c d := by
  obtain ⟨c0, d0, h0⟩ := pqn_pb
  obtain ⟨c1, d1, h1⟩ := tcc_pb
  obtain ⟨c2, d2, h2⟩ := sch_pb
  obtain ⟨c3, d3, h3⟩ := cm_pb
  exact ⟨_, _, fun m n gs i w C U hn hg hx hi he hw hC hU =>
    have hn' : n ≤ m := by omega
    PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      ((const 2 m 0).mul (h0 m n hn')) (h1 m n gs i.val hn' hg hx hi)) (h2 m n (gs.get i) U hU he hn'))
      ((const 4 m 0).mul (pb_var hn'))) ((const 18 m 0).mul (pb_var hU))) (h3 m n (gs.get i) w C hn hw hC))
      ((const 16 m 0).mul (PolyBound.add (pb_var hw) (const 2 m 0)))) (const 93 m 0)⟩

theorem cbr_pb : ∃ c d, ∀ (m : Nat) (words : List (List Bool)) (j : Fin words.length) (B n : Nat)
    (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C U : Nat),
    (words.flatMap frame).length ≤ m → j.val ≤ m → B ≤ m → (words.get j).length ≤ m →
    n+1 ≤ m → gs.length ≤ m → ((gs.take i.val).flatMap exactWord).length ≤ m → i.val ≤ m →
    (exactWord (gs.get i)).length ≤ m → w ≤ m → C ≤ m → U ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_CircuitBaseRun.budget words j B gs i w C U) m c d := by
  obtain ⟨c0, d0, h0⟩ := tfr_pb
  obtain ⟨c1, d1, h1⟩ := sbr_pb
  exact ⟨_, _, fun m words j B n gs i w C U hf hj hB hwj hn hg hx hi he hw hC hU =>
    PolyBound.add (PolyBound.add (PolyBound.add (h0 m words j B hf hj hB hwj)
      (h1 m n gs i w C U hn hg hx hi he hw hC hU)) ((const 6 m 0).mul (pb_var hU))) (const 18 m 0)⟩

theorem dbr_pb : ∃ c d, ∀ (m : Nat) (words : List (List Bool)) (j : Fin words.length) (B n : Nat)
    (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (v w C U : Nat),
    (words.flatMap frame).length ≤ m → j.val ≤ m → B ≤ m → (words.get j).length ≤ m →
    n+1 ≤ m → gs.length ≤ m → ((gs.take i.val).flatMap exactWord).length ≤ m → i.val ≤ m →
    (exactWord (gs.get i)).length ≤ m → v ≤ m → w ≤ m → C ≤ m → U ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_DigitBaseRun.budget words j B gs i v w C U) m c d := by
  obtain ⟨c0, d0, h0⟩ := cbr_pb
  obtain ⟨c1, d1, h1⟩ := mut_pb
  exact ⟨_, _, fun m words j B n gs i v w C U hf hj hB hwj hn hg hx hi he hv hw hC hU =>
    PolyBound.add (PolyBound.add (PolyBound.add (h0 m words j B n gs i w C U hf hj hB hwj hn hg hx hi he hw hC hU)
      (h1 m v i.val hv hi)) ((const 4 m 0).mul (pb_var hU))) (const 13 m 0)⟩

/-! ## 2. Pure facts -/

theorem pad_length_le (U : Nat) (l : List Bool) (h : l.length ≤ U) : (ZeroPadding.pad U l).length ≤ U := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate]
  omega

/-- The ten words the base worker loads for one child (`SelectedBase.Base.words`) fit `U`. -/
theorem masters_len {n : Nat} (g : ExactThresholdGate n) (w C U a : Nat) (he : (exactWord g).length ≤ U)
    (hn : n+2 ≤ U) (hw : 2*(w+2)+1 ≤ U) (hC : C ≤ U) (j : Fin 10) :
    (PCJ45bee56da9f34d5a_SelectedBase.Base.words (ZeroPadding.pad U (exactWord g)) (List.replicate (n+1) true)
      (n+1) w C U a j).length ≤ U := by
  have hs : (frame (SignedSortKey.binary (w+2) a)).length ≤ U := by
    rw [frame_length, SignedSortKey.binary_length]; omega
  have h0 : (frame (SignedSortKey.binary w 0)).length ≤ U := by
    rw [frame_length, SignedSortKey.binary_length]; omega
  fin_cases j <;>
    simp [PCJ45bee56da9f34d5a_CanonicalBaseCell.words, PCJ45bee56da9f34d5a_CellGatePalette.words,
      Fin.addCases, MatrixScoreWeight.scalar, RepairSource.VerifierDecoding.CompareMachine.word] <;>
    first
    | exact pad_length_le U _ he
    | exact pad_length_le U _ hs
    | exact h0
    | omega

/-- The accumulator before circuit `j` never exceeds the final base. -/
theorem acc_le (d : PCJ45bee56da9f34d5a_FourfoldBaseData.Data) (k : Nat) :
    d.acc k ≤ 1 + d.values.sum := by
  have h := List.sum_take_add_sum_drop d.values k
  unfold PCJ45bee56da9f34d5a_FourfoldBaseData.Data.acc
  omega

/-! ## 3. The base worker's numeric premises at the request -/

/-- `m_B(T) := 100T+200`: dominates every size the base budgets read (`w = 12T+17`, `C = 8w+12`, `T`). -/
def mBOf (T : Nat) : Nat := 100*T+200
def DOf (cD dD T : Nat) : Nat := cD*(mBOf T+1)^dD
def UOf' (cD dD cU dU T : Nat) : Nat := cU*(mBOf T+DOf cD dD T+1)^dU
def FOf' (cD dD cU dU cF dF T : Nat) : Nat := cF*(mBOf T+UOf' cD dD cU dU T+1)^dF

end
end RowsConstruction.ThrBaseBounds
