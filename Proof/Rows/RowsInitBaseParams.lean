import Proof.Rows.RowsThrBaseBounds

/-! # Rows initializer: the THR base worker's parameters as CLOSED polynomials (explicit constants)

**Consumer.** The initializer's resident `init` words that RW's `complete` and RC5's key-0 writer read:
`ThrC5Ready`/`K0Ready` (`Proof/Rows/RowsPartsStep.lean`, `Proof/Rows/RowsKeyZeroMode.lean`) demand EXACTLY
`init iOne = pad (ThrSelBase.bU T) (fb wT 1)` and the 78 words `ThrSelBase.baseInit … k`
(`FourfoldBaseCell.bank … (bU T) …`). As verified, `ThrSelBase.bD/bU/bF` (`Proof/Rows/RowsThrSelBase.lean`) are
`Classical.choose` of `ThrBaseBounds.base_numeric`, an existential over FUNCTIONS `ℕ → ℕ` whose spec only bounds them, so
no machine can be proved to write a word of length `bU T`. This module restates `base_numeric` with the existential on
the six CONSTANTS (`DOf cD dD`, `UOf' cD dD cU dU`, `FOf' cD dD cU dU cF dF`, the closed polynomials of
`Proof/Rows/RowsThrBaseBounds.lean`), so the patched `ThrSelBase` §1 can define `bD/bU/bF` as those polynomials at chosen
constants; every downstream statement is unchanged. The proof is `base_numeric`'s, verbatim, with the witness moved.

**Paper.** `paper.tex:1193-1196`, `:2925-2926` (the canonical base of the child tuple; request-level constants prepared
once). **Budget.** None here (a numeric lemma); `baseParams_pb` bounds `D+U+F` by one fixed polynomial of `T`.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.BaseParams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open RowsConstruction RowsConstruction.SymBounds RowsConstruction.ThrBounds RowsConstruction.ThrBaseBounds
noncomputable section

/-- **`base_numeric` with explicit constants**: the three parameter functions are the closed polynomials
`DOf cD dD`, `UOf' cD dD cU dU`, `FOf' cD dD cU dU cF dF` of `T = |input|`. -/
theorem base_numeric_explicit : ∃ cD dD cU dU cF dF : Nat,
    ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (four : r.circuits.length ≤ 4) (L target : Nat) (sel : ThresholdRows.Selection a r),
      PCJ45bee56da9f34d5a_FourfoldBaseData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (ThrWidth.T a r four L target) (12*ThrWidth.T a r four L target+17)
        (8*(12*ThrWidth.T a r four L target+17)+12) (DOf cD dD (ThrWidth.T a r four L target))
        (UOf' cD dD cU dU (ThrWidth.T a r four L target)) (ThrWidth.T a r four L target)
        (FOf' cD dD cU dU cF dF (ThrWidth.T a r four L target)) ∧
      4*(12*ThrWidth.T a r four L target+19)+3 ≤ UOf' cD dD cU dU (ThrWidth.T a r four L target) := by
  obtain ⟨cD, dD, hD⟩ := slb_pb
  obtain ⟨c2, d2, h2⟩ := tfr_pb
  obtain ⟨c3, d3, h3⟩ := mut_pb
  obtain ⟨c4, d4, h4⟩ := pqn_pb
  obtain ⟨c5, d5, h5⟩ := tcc_pb
  obtain ⟨c6, d6, h6⟩ := cm_pb
  obtain ⟨cF, dF, hF⟩ := dbr_pb
  obtain ⟨cU, hcU⟩ : ∃ cU, cU = c2+c3+c4+c5+c6+300 := ⟨_, rfl⟩
  obtain ⟨dU, hdU⟩ : ∃ dU, dU = d2+d3+d4+d5+d6+1 := ⟨_, rfl⟩
  refine ⟨cD, dD, cU, dU, cF, dF, ?_⟩
  intro a r four L target sel
  set T := ThrWidth.T a r four L target with hTdef
  set d := PCJ45bee56da9f34d5a_StreamPair.data a r four sel with hd
  set D := DOf cD dD T with hDdef
  set U := UOf' cD dD cU dU T with hUdef
  set m1 := mBOf T+D with hm1
  have eU : U = cU*(m1+1)^dU := rfl
  have hmB : mBOf T = 100*T+200 := rfl
  -- the U-level linear demand
  have hlin : m1+2 ≤ U := by rw [eU]; exact fit (lin_pb _) (by omega) (by omega)
  -- per-circuit facts (as in `thr_numeric`)
  have har : ∀ j : Fin d.count, 2*d.arity j+2 ≤ T :=
    fun j => arity_le a r four L target (r.circuits.get j) (List.get_mem _ _) _
      (List.get_mem _ (d.selected j))
  have hgl : ∀ j : Fin d.count, (d.gates j).length ≤ T :=
    fun j => ThrWidth.children_length_le a r four L target (r.circuits.get j) (List.get_mem _ _)
  have htk : ∀ (j : Fin d.count) (i : Nat), (((d.gates j).take i).flatMap exactWord).length ≤ T :=
    fun j i => take_le a r four L target (r.circuits.get j) (List.get_mem _ _) i
  have hex : ∀ j : Fin d.count, (exactWord ((d.gates j).get (d.selected j))).length ≤ T :=
    fun j => exactWord_le a r four L target (r.circuits.get j) (List.get_mem _ _) _
      (List.get_mem _ (d.selected j))
  have hsl : ∀ j : Fin d.count, (d.selected j).val < T :=
    fun j => lt_of_lt_of_le (d.selected j).isLt (hgl j)
  have hwf : (d.words.flatMap frame).length ≤ T := words_frame_le a r four L target sel
  have hwl : ∀ j : Fin d.words.length, (d.words.get j).length ≤ T :=
    fun j => word_le a r four L target sel _ (List.get_mem _ _)
  have hmag : ∀ j : Fin d.count, childMagnitude ((d.gates j).get (d.selected j)) < 2^T :=
    fun j => ThrWidth.childMagnitude_lt a r four L target (r.circuits.get j) (List.get_mem _ _) _
      (List.get_mem _ (d.selected j))
  have hrad : 1 + d.values.sum < 2^(T+2) := ThrWidth.radix_lt a r four L target sel
  have hTw : 2^T ≤ 2^(12*T+17) := Nat.pow_le_pow_right (by decide) (by omega)
  have hTw2 : 2^(T+2) ≤ 2^(12*T+17+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hc4 : d.count ≤ 4 := d.count_le
  refine ⟨⟨fun y hy => word_le a r four L target sel y hy,
    fun j => ?_, fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩, ?_⟩
  -- top_cost
  · have := j.isLt
    simp only [PCJ45bee56da9f34d5a_FourfoldBaseData.words_length] at this
    exact fit (PolyBound.add (h2 m1 d.words j T (by omega) (by omega) (by omega) (by have := hwl j; omega))
      (const 2 m1 0)) (by omega) (by omega)
  -- LocalBounds: digit_fit
  · exact lt_of_lt_of_le (hsl j) (Nat.lt_two_pow_self).le
  -- digit_cost
  · exact fit (PolyBound.add (h3 m1 T _ (by omega) (by have := hsl j; omega)) (const 1 m1 0)) (by omega) (by omega)
  -- arity_cost
  · exact fit (PolyBound.add (h4 m1 _ (by have := har j; omega)) (const 1 m1 0)) (by omega) (by omega)
  -- payload_fit
  · have hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload (d.gates j)).length ≤ T :=
      word_le a r four L target sel _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    omega
  -- cursor_cost
  · exact fit (PolyBound.add (h5 m1 _ _ _ (by have := har j; omega) (by have := hgl j; omega)
      (by have := htk j (d.selected j).val; omega) (by have := hsl j; omega)) (const 1 m1 0)) (by omega) (by omega)
  -- gate_fit
  · have := hex j
    omega
  -- weight_fit
  · intro x hx
    simp only [C10ThresholdChildMagnitude.items, C10ThresholdChildMagnitude.fields, List.mem_map,
      List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have := hex j
    rcases hz with ⟨k, rfl⟩ | rfl
    · have := weight_le_exactWord ((d.gates j).get (d.selected j)) k
      dsimp only
      omega
    · have := target_le_exactWord ((d.gates j).get (d.selected j))
      dsimp only
      omega
  -- magnitude_fit
  · exact lt_of_lt_of_le (hmag j) hTw
  -- score_cost
  · have hx : (C10ThresholdChildMagnitude.items ((d.gates j).get (d.selected j))).length ≤ mBOf T := by
      rw [items_length]; have := har j; omega
    exact hD (mBOf T) _ _ _ hx (by omega) (by omega)
  -- clock_cap
  · omega
  -- score_cap
  · omega
  -- result_fit
  · have hn := PCJ45bee56da9f34d5a_FourfoldBaseData.acc_next d j
    have hle := acc_le d (j.val+1)
    omega
  -- magnitude_cost
  · exact fit (PolyBound.add (h6 m1 _ _ _ _ (by have := har j; omega) (by omega) (by omega)) (const 2 m1 0))
      (by omega) (by omega)
  -- masters_fit
  · intro k
    exact masters_len _ _ _ U _ (by have := hex j; omega) (by have := har j; omega) (by omega) (by omega) k
  -- cell_cost
  · have hj := j.isLt
    have hU2 : U ≤ mBOf T + U := by omega
    exact hF (mBOf T + U) d.words ⟨j.val, by simp⟩ T _ (d.gates j) (d.selected j) T (12*T+17)
      (8*(12*T+17)+12) U (by omega) (by show j.val ≤ _; omega) (by omega) (by have := hwl ⟨j.val, by simp⟩; omega)
      (by have := har j; omega) (by have := hgl j; omega) (by have := htk j (d.selected j).val; omega)
      (by have := hsl j; omega) (by have := hex j; omega) (by omega) (by omega) (by omega) hU2
  -- the scalar copy fits
  · omega

end
end RowsInit.BaseParams
