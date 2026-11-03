import Proof.Rows.RowsSymVerdict
import Proof.MachineModel.BlockPolyBound

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline
noncomputable section

theorem pb_var {v m : Nat} (h : v ≤ m) : PolyBounded v m 1 1 := by
  unfold PolyBounded; rw [pow_one]; omega

theorem pb_sq {v m c d : Nat} (h : PolyBounded v m c d) : PolyBounded (v^2) m (c*c) (d+d) := by
  rw [pow_two]; exact h.mul h

/-- `a+1+b` (sequential composition). -/
theorem J {m a b ca cb da db : Nat} (ha : PolyBounded a m ca da) (hb : PolyBounded b m cb db) :
    PolyBounded (a+1+b) m (ca+1+cb) (max (max da 0) db) :=
  PolyBound.add (PolyBound.add ha (const 1 m 0)) hb

/-- `2*a+2` (a masked stage). -/
theorem two {m a ca da : Nat} (ha : PolyBounded a m ca da) :
    PolyBounded (2*a+2) m (2*ca+2) (max (0+da) 0) :=
  PolyBound.add ((const 2 m 0).mul ha) (const 2 m 0)

theorem natBitLength_le (n : Nat) : natBitLength n ≤ n+1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem nbl_pb {m n : Nat} (h : n ≤ m) : PolyBounded (natBitLength n) m 1 1 := by
  have := natBitLength_le n
  unfold PolyBounded; rw [pow_one]; omega

theorem gate_pb {m B q : Nat} (hB : B ≤ m) (hq : q ≤ m) :
    PolyBounded (B+q+(B+1)+1) m (1+1+(1+1)+1) (max (max (max 1 1) (max 1 1)) 1) :=
  PolyBound.add (PolyBound.add (PolyBound.add (pb_var hB) (pb_var hq))
    (PolyBound.add (pb_var hB) (const 1 m 1))) (const 1 m 1)

/-- `2048*(B+q+(B+1)+1)^2`, the flag bank's uniform gate capacity. -/
theorem U_pb : ∃ c d, ∀ m B q : Nat, B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_UniformMinimumBounds.U B q (B+1)) m c d :=
  ⟨_, _, fun m _ _ hB hq => (const 2048 m 0).mul (pb_sq (gate_pb hB hq))⟩

theorem cgc_pb : ∃ c d, ∀ m B q : Nat, B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_CountedGateCell.cost B q (B+1)) m c d :=
  ⟨_, _, fun m _ _ hB hq => PolyBound.add ((const 131072 m 0).mul (pb_sq (gate_pb hB hq))) (const 2 m 0)⟩

theorem ngl_pb : ∃ c d, ∀ m B q : Nat, B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_NativeGateLoop.budget B B q) m c d := by
  obtain ⟨c0, d0, h0⟩ := cgc_pb
  exact ⟨_, _, fun m B q hB hq =>
    PolyBound.add ((pb_var hB).mul (PolyBound.add (h0 m B q hB hq) (const 3 m 0))) (const 3 m 0)⟩

theorem uniform_pb : ∃ c d, ∀ m B q : Nat, B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_CircuitFlagCost.uniform B q) m c d := by
  obtain ⟨c1, d1, h1⟩ := U_pb
  obtain ⟨c2, d2, h2⟩ := ngl_pb
  exact ⟨_, _, fun m B q hB hq =>
    PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      ((const 2 m 0).mul (PolyBound.add (PolyBound.add (PolyBound.add
        ((pb_var hB).mul (PolyBound.add ((const 8 m 0).mul (PolyBound.add (pb_var hB) (const 1 m 1)))
          (const 10 m 0)))
        ((const 14 m 0).mul (PolyBound.add (pb_var hB) (const 1 m 1)))) (pb_var hB)) (const 25 m 0)))
      ((const 10 m 0).mul (h1 m B q hB hq))) ((const 2 m 0).mul (PolyBound.add (pb_var hB) (const 1 m 1))))
      ((const 10 m 0).mul (pb_var hB))) (h2 m B q hB hq)) (const 42 m 0)⟩

theorem nfl_pb : ∃ c d, ∀ m N B q : Nat, N ≤ m → B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_NativeFlagsLoop.budget N B q) m c d := by
  obtain ⟨c0, d0, h0⟩ := uniform_pb
  exact ⟨_, _, fun m N B q hN hB hq =>
    PolyBound.add ((pb_var hN).mul (PolyBound.add (h0 m B q hB hq) (const 3 m 0))) (const 3 m 0)⟩

theorem ccc_pb : ∃ c d, ∀ m tag q L target N : Nat, tag ≤ m → q ≤ m → natBitLength L ≤ m →
    natBitLength target ≤ m → N ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N) m c d :=
  ⟨_, _, fun m _ _ _ _ _ htag hq hL ht hN =>
    PolyBound.add ((const 2 m 0).mul (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      (nbl_pb htag) (nbl_pb hq)) (pb_var hL)) (pb_var ht)) (nbl_pb hN))) (const 19 m 0)⟩

theorem pqn_pb : ∃ c d, ∀ m N : Nat, N ≤ m → PolyBounded (PCPPQueryNatural.budget N) m c d :=
  ⟨_, _, fun m _ hN =>
    PolyBound.add (PolyBound.add (PolyBound.add
      ((pb_var hN).mul (PolyBound.add ((const 8 m 0).mul (nbl_pb hN)) (const 10 m 0)))
      ((const 14 m 0).mul (nbl_pb hN))) (pb_var hN)) (const 25 m 0)⟩

theorem nff_pb : ∃ c d, ∀ m tag q L target N B : Nat, tag ≤ m → q ≤ m → natBitLength L ≤ m →
    natBitLength target ≤ m → N ≤ m → B ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_NativeFamilyFlags.budget tag q L target N B) m c d := by
  obtain ⟨c1, d1, h1⟩ := ccc_pb
  obtain ⟨c2, d2, h2⟩ := pqn_pb
  obtain ⟨c3, d3, h3⟩ := U_pb
  obtain ⟨c4, d4, h4⟩ := nfl_pb
  exact ⟨_, _, fun m tag q L target N B htag hq hL ht hN hB =>
    PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      (h1 m tag q L target N htag hq hL ht hN) ((const 2 m 0).mul (h2 m N hN)))
      ((const 8 m 0).mul (h3 m B q hB hq))) (const 21 m 0)) (h4 m N B q hN hB hq)) (const 3 m 0)⟩

theorem countFlags_pb : ∃ c d, ∀ m N w : Nat, N ≤ m → w ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_CountFlags.budget N w) m c d :=
  ⟨_, _, fun m _ _ hN hw =>
    PolyBound.add ((pb_var hN).mul (PolyBound.add ((const 4 m 0).mul (pb_var hw)) (const 11 m 0)))
      (const 3 m 0)⟩

/-- **The SYM cell verdict's cost is one fixed polynomial of any measure dominating its sizes.** -/
theorem cost_pb : ∃ c d, ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (m L target T w : Nat),
    r.q ≤ m → natBitLength L ≤ m → natBitLength target ≤ m → (SymMeaning.circuits r).length ≤ m →
    T ≤ m → w ≤ m → 4 ≤ m → (∀ c : Fin 4, SymVerdict.N r c ≤ m) →
    PolyBounded (SymVerdict.cost r L target T w) m c d := by
  obtain ⟨c1, d1, h1⟩ := nff_pb
  obtain ⟨c2, d2, h2⟩ := countFlags_pb
  exact ⟨_, _, fun r m L target T w hq hL ht hN hT hw h4 hNc =>
    have hw1 := PolyBound.add ((const 2 m 0).mul (pb_var hw)) (const 1 m 1)
    have cmp := two (J hw1 (J hw1 (J hw1 hw1)))
    J (two (h1 m 0 r.q L target _ T (Nat.zero_le _) hq hL ht hN hT))
      (J (two (h2 m _ w (hNc 0) hw))
        (J (two (h2 m _ w (hNc 1) hw))
          (J (two (h2 m _ w (hNc 2) hw))
            (J (two (h2 m _ w (hNc 3) hw))
              (J cmp (J (two (h2 m 4 w h4 hw)) (two hw1)))))))⟩

/-! ## Encoding facts: every SYM size is bounded by the native word, which is bounded by `|input|` -/

theorem native_le_input (a : DecompositionAlgorithm) (r : PCJd4d1d9d7d1fa4313_Production.Request) :
    r.nativeWord.length ≤ (r.input a).length := by
  simp only [PCJd4d1d9d7d1fa4313_Production.Request.input, List.length_append, frame_length]
  omega

theorem header_le (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : Nat) :
    2*natBitLength r.q+1 + (2*natBitLength L+1) + (2*natBitLength target+1) ≤
      (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).nativeWord.length := by
  simp only [PCJd4d1d9d7d1fa4313_Production.Request.nativeWord, List.length_append,
    DecompositionSource.natWord_length]
  omega

theorem block_le_payload {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) :
    (SymMeaning.symGates c).length+1 ≤ (frame (PCJd4d1d9d7d1fa4313_Production.symWord c)).length := by
  have hb : (SymMeaning.symGates c).length ≤
      ((List.ofFn c.bottom).flatMap (fun g => frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g))).length := by
    rw [SymMeaning.symGates, List.length_ofFn, List.length_flatMap]
    calc c.bottomCount = ((List.ofFn c.bottom).map (fun _ => 1)).sum := by
          rw [List.map_ofFn, List.sum_ofFn]; simp
      _ ≤ ((List.ofFn c.bottom).map (fun g => (frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g)).length)).sum := by
        apply List.sum_le_sum
        intro g _
        rw [frame_length]; omega
  simp only [frame_length, PCJd4d1d9d7d1fa4313_Production.symWord, List.length_append] at hb ⊢
  omega

/-- The flag blocks (bottom-gate flags plus one target flag per circuit) fit in the native word. -/
theorem flagged_le_native (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : Nat) (I : Finset (Fin r.q)) (x : BitInput r.q) :
    (SymMeaning.flagged (r.circuits.map (fun k => SymMeaning.block k I x))).length ≤
      (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).nativeWord.length := by
  rw [SymMeaning.flagged_length, List.map_map]
  have h1 : (r.circuits.map ((fun b => b.length+1) ∘ fun k => SymMeaning.block k I x)).sum ≤
      (r.circuits.map (fun c => (frame (PCJd4d1d9d7d1fa4313_Production.symWord c)).length)).sum := by
    apply List.sum_le_sum
    intro c _
    simp only [Function.comp, SymMeaning.block, List.length_map]
    exact block_le_payload c
  have h2 : (r.circuits.map (fun c => (frame (PCJd4d1d9d7d1fa4313_Production.symWord c)).length)).sum =
      (r.circuits.flatMap (fun c => frame (PCJd4d1d9d7d1fa4313_Production.symWord c))).length := by
    rw [List.length_flatMap]
  have h3 : (r.circuits.flatMap (fun c => frame (PCJd4d1d9d7d1fa4313_Production.symWord c))).length ≤
      (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).nativeWord.length := by
    simp only [PCJd4d1d9d7d1fa4313_Production.Request.nativeWord, List.length_append]
    omega
  omega

/-- Cumulative targets never exceed cumulative drivers when every offset is at most its circuit's gate
count (true of every `symFamily` row: `symOffsetList`). -/
theorem targetCount_le_driverLen (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (offset : Fin r.circuits.length → Nat)
    (hoff : ∀ c, offset c ≤ (SymMeaning.symGates (r.circuits.get c)).length) (c : Nat) :
    SymMeaning.targetCount r offset c ≤ SymMeaning.driverLen r c := by
  unfold SymMeaning.targetCount SymMeaning.driverLen
  by_cases hc : c < r.circuits.length
  · rw [if_pos hc, if_pos hc]
    have hle : ∀ i, SymMeaning.offsetN r offset i ≤ SymMeaning.gateCount r i := by
      intro i
      unfold SymMeaning.offsetN SymMeaning.gateCount
      by_cases hi : i < r.circuits.length
      · rw [dif_pos hi]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
          Option.map_some, Option.getD_some]
        exact hoff ⟨i, hi⟩
      · rw [dif_neg hi]; exact Nat.zero_le _
    have hs : (∑ i ∈ Finset.range c, (SymMeaning.offsetN r offset i + 1)) ≤
        (∑ i ∈ Finset.range c, (SymMeaning.gateCount r i + 1)) :=
      Finset.sum_le_sum (fun i _ => by have := hle i; omega)
    have := hle c
    omega
  · rw [if_neg hc, if_neg hc]

/-! ## C3(e) for SYM: every numeric premise of the SYM cell, at request-sized parameters -/

/-- **SYM numeric premises.** One closed pair `(c, d)` such that, for every SYM request and every row
offset tuple within the circuits' gate counts, with `T := |input|`, `w := T+3` and `S := q+|input|`,
all numeric hypotheses of `RowsSymVerdict.run`/`ModeMasks.sym_gmask` hold with the shared log capacity
`cap := c*(S+5)^d`, and the per-cell verdict cost is at most that same polynomial of `S`. -/
theorem sym_numeric : ∃ c d, ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat) (offset : Fin r.circuits.length → Nat),
    (∀ k, offset k ≤ (SymMeaning.symGates (r.circuits.get k)).length) →
    let T := ((PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).input a).length
    let w := T+3
    let cap := c*(r.q+T+5)^d
    (SymVerdict.src r L target).length ≤ T ∧ 4 < 2^w ∧ (∀ k : Fin 4, SymVerdict.N r k < 2^w) ∧
    (∀ k : Fin 4, SymVerdict.Tg r offset k < 2^w) ∧
    PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T ≤ cap ∧
    (∀ k : Fin 4, PCJ45bee56da9f34d5a_CountFlags.budget (SymVerdict.N r k) w ≤ cap) ∧
    (2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))) ≤ cap ∧
    PCJ45bee56da9f34d5a_CountFlags.budget 4 w ≤ cap ∧
    SymVerdict.cost r L target T w ≤ cap := by
  obtain ⟨c, d, hpb⟩ := cost_pb
  refine ⟨c, d, fun a r four L target offset hoff => ?_⟩
  intro T w cap
  have hnat : (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).nativeWord.length ≤ T :=
    native_le_input a _
  have hsrc : (SymVerdict.src r L target).length ≤ T := by
    rw [SymVerdict.src, SymMeaning.native_eq r four L target]; exact hnat
  have hhead := header_le r four L target
  have hflag := flagged_le_native r four L target ∅ (fun _ => false)
  have hN : ∀ k : Fin 4, SymVerdict.N r k ≤ T+1 := by
    intro k
    have h := SymMeaning.driverLen_le r ∅ (fun _ => false) k.val
    rw [List.length_append, List.length_singleton] at h
    unfold SymVerdict.N
    omega
  have hTg : ∀ k : Fin 4, SymVerdict.Tg r offset k ≤ T+1 := fun k =>
    (targetCount_le_driverLen r offset hoff k.val).trans (hN k)
  have hpow : T+1 < 2^w := by
    have h1 := Nat.lt_two_pow_self (n := w)
    have hwT : w = T+3 := rfl
    omega
  have hw4 : 4 < 2^w := by
    have h8 : 2^3 ≤ 2^w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hcost : SymVerdict.cost r L target T w ≤ cap := by
    have h := hpb r (r.q+T+4) L target T w (by omega) (by omega) (by omega)
      (by simp only [SymMeaning.circuits, List.length_map]; omega) (by omega) (by omega) (by omega)
      (fun k => by have := hN k; omega)
    unfold PolyBounded at h
    simpa [cap] using h
  refine ⟨hsrc, hw4, fun k => lt_of_le_of_lt (hN k) hpow, fun k => lt_of_le_of_lt (hTg k) hpow,
    ?_, ?_, ?_, ?_, hcost⟩
  · refine le_trans ?_ hcost
    unfold SymVerdict.cost
    omega
  · intro k
    refine le_trans ?_ hcost
    unfold SymVerdict.cost
    fin_cases k <;> simp <;> omega
  · refine le_trans ?_ hcost
    unfold SymVerdict.cost SymVerdict.cmpCost
    omega
  · refine le_trans ?_ hcost
    unfold SymVerdict.cost
    omega

end
end RowsConstruction.SymBounds
