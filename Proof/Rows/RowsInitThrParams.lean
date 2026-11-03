import Proof.Rows.RowsThrBounds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.ThrParams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.RepairSource.CloseoutFinal
open RowsConstruction RowsConstruction.SymBounds RowsConstruction.ThrBounds
noncomputable section

/-- **THR numeric premises with computable `U`, `F`.** Exactly `ThrBounds.thr_numeric`'s conclusion at
`Uf := UOf cU dU`, `Ff := FOf cF dF` for some constants. -/
theorem thr_numeric_explicit : ∃ cU dU cF dF : Nat, ∃ Pf Bf : Nat → Nat → Nat,
    (∃ c d, ∀ q T : Nat, PolyBounded (UOf cU dU q T+FOf cF dF q T+Pf q T+Bf q T) (q+T) c d) ∧
    ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (four : r.circuits.length ≤ 4) (L target : Nat) (sel : ThresholdRows.Selection a r) (cutoff : Nat),
      cutoff = CloseoutFinalC10ThresholdRows.primeCutoff a r target →
      ∀ (prime : PrimeIndex cutoff) (o : Fin prime.val),
      (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ ThrWidth.T a r four L target ∧
      PCJ45bee56da9f34d5a_FourfoldPowerData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val (12*ThrWidth.T a r four L target+19)
        (FOf cF dF r.q (ThrWidth.T a r four L target)) (UOf cU dU r.q (ThrWidth.T a r four L target))
        (ThrWidth.T a r four L target) (ThrWidth.T a r four L target) (Pf r.q (ThrWidth.T a r four L target)) ∧
      (PCJ45bee56da9f34d5a_StreamPairPorts.coefficientWord (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val (12*ThrWidth.T a r four L target+19)
        o.val).length ≤ UOf cU dU r.q (ThrWidth.T a r four L target) ∧
      (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ UOf cU dU r.q (ThrWidth.T a r four L target) ∧
      (∀ (I : Finset (Fin r.q)) (x : BitInput r.q),
        (PCJ45bee56da9f34d5a_StreamPair.flags r I x).length+1 ≤ UOf cU dU r.q (ThrWidth.T a r four L target)) ∧
      (∀ (I : Finset (Fin r.q)) (x : BitInput r.q),
        PCJ45bee56da9f34d5a_ThresholdTraversal.budget a r sel I x (ThrWidth.T a r four L target) L target
          (12*ThrWidth.T a r four L target+19) (UOf cU dU r.q (ThrWidth.T a r four L target))
          (Pf r.q (ThrWidth.T a r four L target)) ≤ Bf r.q (ThrWidth.T a r four L target)) := by
  obtain ⟨c1, d1, h1⟩ := cap_pb
  obtain ⟨c2, d2, h2⟩ := tfr_pb
  obtain ⟨c3, d3, h3⟩ := mut_pb
  obtain ⟨c4, d4, h4⟩ := pqn_pb
  obtain ⟨c5, d5, h5⟩ := tcc_pb
  obtain ⟨c6, d6, h6⟩ := cw_pb
  obtain ⟨cc, dc, hc⟩ := core_pb
  obtain ⟨cp, dp, hp⟩ := cpr_pb
  obtain ⟨cb, db, hbt⟩ := tt_pb
  obtain ⟨cU, hcU⟩ : ∃ cU, cU = c1+c2+c3+c4+c5+c6+10 := ⟨_, rfl⟩
  obtain ⟨dU, hdU⟩ : ∃ dU, dU = d1+d2+d3+d4+d5+d6+1 := ⟨_, rfl⟩
  refine ⟨cU, dU, cc+1, dc, fun q T => POf cU dU (cc+1) dc cp dp q T,
    fun q T => BOf cU dU (cc+1) dc cp dp cb db q T, params_pb cU dU (cc+1) dc cp dp cb db, ?_⟩
  intro a r four L target sel cutoff hcut prime o
  beta_reduce
  have hhead := header_le a r four L target
  have hnat := native_le a r four L target
  have e1 : m1Of r.q (ThrWidth.T a r four L target) = r.q+(12*ThrWidth.T a r four L target+19) := rfl
  have e2 : m2Of cU dU (cc+1) dc r.q (ThrWidth.T a r four L target) = m1Of r.q (ThrWidth.T a r four L target) +
      UOf cU dU r.q (ThrWidth.T a r four L target) + FOf (cc+1) dc r.q (ThrWidth.T a r four L target) := rfl
  -- the U-level linear demand
  have hlin : m1Of r.q (ThrWidth.T a r four L target)+2 ≤ UOf cU dU r.q (ThrWidth.T a r four L target) :=
    fit (lin_pb _) (by omega) (by omega)
  have hT1 : ThrWidth.T a r four L target+2 ≤ UOf cU dU r.q (ThrWidth.T a r four L target) := by omega
  have hw1 : 12*ThrWidth.T a r four L target+19 ≤ m1Of r.q (ThrWidth.T a r four L target) := by omega
  have hTm : ThrWidth.T a r four L target ≤ m1Of r.q (ThrWidth.T a r four L target) := by omega
  -- per-circuit facts, stated at the data's own projections
  have har : ∀ j : Fin (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count,
      2*(PCJ45bee56da9f34d5a_StreamPair.data a r four sel).arity j+2 ≤ ThrWidth.T a r four L target :=
    fun j => arity_le a r four L target (r.circuits.get j) (List.get_mem _ _) _
      (List.get_mem _ ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j))
  have hgl : ∀ j : Fin (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count,
      ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).gates j).length ≤ ThrWidth.T a r four L target :=
    fun j => ThrWidth.children_length_le a r four L target (r.circuits.get j) (List.get_mem _ _)
  have htk : ∀ (j : Fin (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count) (i : Nat),
      ((((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).gates j).take i).flatMap exactWord).length ≤
        ThrWidth.T a r four L target :=
    fun j i => take_le a r four L target (r.circuits.get j) (List.get_mem _ _) i
  have hex : ∀ j : Fin (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count,
      (exactWord (((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).gates j).get
        ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j))).length ≤ ThrWidth.T a r four L target :=
    fun j => exactWord_le a r four L target (r.circuits.get j) (List.get_mem _ _) _
      (List.get_mem _ ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j))
  have hsl : ∀ j : Fin (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count,
      ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j).val < ThrWidth.T a r four L target :=
    fun j => lt_of_lt_of_le ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j).isLt (hgl j)
  have hwf := words_frame_le a r four L target sel
  have hwl : ∀ j : Fin (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.length,
      ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.get j).length ≤ ThrWidth.T a r four L target :=
    fun j => word_le a r four L target sel _ (List.get_mem _ _)
  have hcount : (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count ≤ 4 := four
  -- the coefficient word
  have hcw : (PCJ45bee56da9f34d5a_StreamPairPorts.coefficientWord (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
      (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val (12*ThrWidth.T a r four L target+19)
      o.val).length ≤ 4*(ThrWidth.T a r four L target*(2*(12*ThrWidth.T a r four L target+19)+1))+
        (2*(12*ThrWidth.T a r four L target+19)+1) := by
    have hs := stream_le (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
      (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val (12*ThrWidth.T a r four L target+19)
      (ThrWidth.T a r four L target) (fun j => by have := har j; omega) 4
    simp only [PCJ45bee56da9f34d5a_StreamPairPorts.coefficientWord, List.length_append, frame_length,
      SignedSortKey.binary_length]
    omega
  refine ⟨hnat, ⟨(mem_primesUpTo.mp prime.property).1.pos,
    ThrWidth.prime_fit a r four L target cutoff hcut prime, ThrWidth.base_fit a r four L target sel,
    fit (PolyBound.add (h1 _ _ hw1) (const 2 _ 0)) (by omega) (by omega),
    fun y hy => word_le a r four L target sel y hy,
    fun j => fit (PolyBound.add (h2 _ _ j _ (by omega) (by have := j.isLt; simp at this; omega) hTm
      (by have := hwl j; omega)) (const 2 _ 0)) (by omega) (by omega),
    fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩,
    le_trans hcw (fit (h6 _ _ _ hTm hw1) (by omega) (by omega)), by omega, fun I x => ?_, fun I x => ?_⟩
  -- LocalBounds
  · exact lt_of_lt_of_le (hsl j) (Nat.lt_two_pow_self).le
  · exact fit (PolyBound.add (h3 _ _ _ hTm (by have := hsl j; omega)) (const 1 _ 0)) (by omega) (by omega)
  · exact fit (PolyBound.add (h4 _ _ (by have := har j; omega)) (const 1 _ 0)) (by omega) (by omega)
  · have := word_le a r four L target sel _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    omega
  · exact fit (PolyBound.add (h5 _ _ _ _ (by have := har j; omega) (by have := hgl j; omega)
      (by have := htk j ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j).val; omega)
      (by have := hsl j; omega)) (const 1 _ 0)) (by omega) (by omega)
  · have := hex j
    omega
  · intro k
    have hk := weight_le_exactWord (((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).gates j).get
      ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j)) k
    have := hex j
    exact fit (PolyBound.add (hc _ false _ _ hw1 (by omega)) (const 1 _ 0)) (by omega) (by omega)
  · have hk := target_le_exactWord (((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).gates j).get
      ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j))
    have := hex j
    exact fit (PolyBound.add (hc _ true _ _ hw1 (by omega)) (const 1 _ 0)) (by omega) (by omega)
  -- cell cost
  · have hk := target_le_exactWord (((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).gates j).get
      ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j))
    have := hex j
    have := har j
    have := hgl j
    have := hsl j
    have := htk j ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).selected j).val
    have := hwl ⟨j.val, by simp⟩
    have := j.isLt
    exact hp (m2Of cU dU (cc+1) dc r.q (ThrWidth.T a r four L target)) _ _ _ _ _ _ _ _ _ _
      (by omega) (by rw [Fin.val_mk]; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  -- flags
  · have := flags_le a r four L target I x
    omega
  -- traversal budget
  · have := count_le a r four L target sel I x
    have hN : (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r).length ≤ 4 := by
      simp only [PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits, List.length_map]; exact four
    have e3 : POf cU dU (cc+1) dc cp dp r.q (ThrWidth.T a r four L target) =
        cp*(m2Of cU dU (cc+1) dc r.q (ThrWidth.T a r four L target)+1)^dp := rfl
    exact hbt a r sel I x (m2Of cU dU (cc+1) dc r.q (ThrWidth.T a r four L target) +
      POf cU dU (cc+1) dc cp dp r.q (ThrWidth.T a r four L target)) _ L target _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)


end
end RowsInit.ThrParams
