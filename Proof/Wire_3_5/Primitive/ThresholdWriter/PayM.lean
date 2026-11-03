import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront
import Proof.Wire_3_5.Primitive.SeedFix.TabThrBlock
import Proof.SourceAssembly.SourceTopNative

/-! # THR, TopFront part 1: one circuit's native word and top payload (`payM`, `pay_step`)

P3:2543-2551 (row:threshold-rows) and P3:3071-3091: a THR circuit, given by its code, is decoded to its native word
`thrWord c` (the verified decode block `ThrTab.thrBlockM`, base's THR decoder chain), and its retained top is
decomposed by the algorithm (base `SourceTopNative`: the constructor on `thresholdWord (retainedTop c)`, its output
framed): `payOf alg c = frame (natWord |supp(top c)| ++ exactListWord (children alg c))`.

* `payM a` on `1781 + (T_a − 1)` tapes: the block on tapes `0 … 1780`, then the top machine with its tape `0` on the
  block's tape `1692` (where `thrWord c` lands) and its other tapes on fresh tapes;
* **`pay_step`**: from the block's entry (`frame (natWord code)`, `1^n`, `1^L`, the cell `[false]`), within
  `thrBlockCost c L + 1 + topBudget a c`, every head at `0`, `payOf a c` on `outTop a`, `thrWord c` on tape `1692`, the
  inputs kept on tapes `0 … 2`.

Paper quantities of the main type: one circuit's retained top children (`payOf`) and native word. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.PayM
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5.PrimT

variable (a : DecompositionAlgorithm)

/-- The top machine's tape count. -/
abbrev Ta : ℕ := PCJ6e421fabe2aa4155_SourceTopNative.tapes a

/-- The payload machine's tape count. -/
abbrev PT : ℕ := 1781 + (Ta a - 1)

theorem Ta_ge : 4 ≤ Ta a := by unfold Ta PCJ6e421fabe2aa4155_SourceTopNative.tapes; omega

/-- The block's tapes. -/
def blkMap (j : Fin 1781) : Fin (PT a) := Fin.castAdd _ j

/-- The top machine's tapes: tape `0` on the block's `1692`, the others fresh. -/
def topMap (j : Fin (Ta a)) : Fin (PT a) :=
  if h : j.val = 0 then ⟨1692, by show 1692 < 1781 + (Ta a - 1); omega⟩
  else ⟨1781 + (j.val - 1), by have := j.isLt; show 1781 + (j.val - 1) < 1781 + (Ta a - 1); omega⟩

theorem blkMap_inj : Function.Injective (blkMap a) := fun x y h => by
  have := congrArg Fin.val h
  exact Fin.ext (by simpa [blkMap] using this)

theorem topMap_inj : Function.Injective (topMap a) := by
  intro x y h
  have hv := congrArg Fin.val h
  unfold topMap at hv
  split_ifs at hv with h1 h2 h2 <;> simp at hv <;> apply Fin.ext <;> omega

theorem topMap_zero : topMap a ⟨0, by have := Ta_ge a; omega⟩ = ⟨1692, by show 1692 < 1781 + (Ta a - 1); omega⟩ := by simp [topMap]

theorem topMap_ne_low (j : Fin (Ta a)) (i : Fin (PT a)) (hi : i.val < 1781) (h : i.val ≠ 1692) : topMap a j ≠ i := by
  intro e
  have hv := congrArg Fin.val e
  unfold topMap at hv
  split_ifs at hv <;> simp at hv <;> omega

/-- **One circuit's payload machine**: the decode block, then base's top decomposition on the block's native word. -/
noncomputable def payM :=
  Composition.machine (RecoveryFocus.machine (blkMap a) ThrTab.thrBlockM)
    (RecoveryFocus.machine (topMap a) (PCJ6e421fabe2aa4155_SourceTopNative.machine a))

/-- The payload machine's entry: the block's entry, the fresh tapes blank. -/
def payIn (code n L : ℕ) : Fin (PT a) → List Bool := fun i =>
  if h : i.val < 1781 then ThrTab.blockIn code n L ⟨i.val, h⟩ else []

/-- The top's output tape. -/
def outTop : Fin (PT a) :=
  topMap a (PCJ6e421fabe2aa4155_SourceTopNative.slots a ((0 : Fin 2).natAdd (DecompositionSource.Counted.tapes a + 2)))

/-- The top machine's budget at a circuit. -/
noncomputable def topBudget {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : ℕ :=
  PCJ6e421fabe2aa4155_SourceTopNative.budget a c.top.wireCount
    ⟨c.top.support.card, CompilerSemantics.nonStrictAsStrict (retainedTopGate c)⟩

theorem outTop_ge : 1781 ≤ (outTop a).val := by
  unfold outTop topMap PCJ6e421fabe2aa4155_SourceTopNative.slots
  simp

theorem payIn_blk (code n L : ℕ) (j : Fin 1781) : payIn a code n L (blkMap a j) = ThrTab.blockIn code n L j := by
  unfold payIn blkMap
  rw [dif_pos (by simp)]
  rfl

theorem payIn_hi (code n L : ℕ) (i : Fin (PT a)) (h : 1781 ≤ i.val) : payIn a code n L i = [] := by
  unfold payIn
  rw [dif_neg (by omega)]

/-- Stage 1: the block, docked. -/
theorem blk_step {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ) (o1 : Fin 1781 → List Bool)
    (s1 : Step ThrTab.thrBlockM (ThrTab.thrBlockCost c L) (fun _ => 0)
      (ThrTab.blockIn (encodeNormalizedThresholdThresholdCircuit c) n L) (fun _ => 0) o1) :
    Step (RecoveryFocus.machine (blkMap a) ThrTab.thrBlockM) (ThrTab.thrBlockCost c L) (fun _ => 0)
      (payIn a (encodeNormalizedThresholdThresholdCircuit c) n L) (fun _ => 0)
      (install (blkMap a) (payIn a (encodeNormalizedThresholdThresholdCircuit c) n L) o1) := by
  have d1 := s1.dock (blkMap a) (blkMap_inj a) (fun _ => 0)
    (payIn a (encodeNormalizedThresholdThresholdCircuit c) n L) (fun _ => rfl) (fun j => payIn_blk a _ n L j)
  rw [dockH_existing (blkMap a) (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at d1
  exact d1

/-- The top machine sees `thrWord c` on its tape `0`, blanks elsewhere. -/
theorem top_input {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ) (o1 : Fin 1781 → List Bool)
    (h1692 : o1 ⟨1692, by omega⟩ = PCJd4d1d9d7d1fa4313_Production.thrWord c) (j : Fin (Ta a)) :
    install (blkMap a) (payIn a (encodeNormalizedThresholdThresholdCircuit c) n L) o1 (topMap a j) =
      if j.val = 0 then PCJd4d1d9d7d1fa4313_Production.thrWord c else [] := by
  by_cases hj : j.val = 0
  · rw [if_pos hj]
    have e : topMap a j = blkMap a ⟨1692, by omega⟩ := by
      unfold topMap blkMap; rw [dif_pos hj]; rfl
    rw [e, install_slot _ (blkMap_inj a)]
    exact h1692
  · rw [if_neg hj]
    have hge : 1781 ≤ (topMap a j).val := by unfold topMap; rw [dif_neg hj]; simp
    rw [install_other _ _ _ _ (fun k e => by
      have := congrArg Fin.val e
      simp only [blkMap, Fin.val_castAdd] at this
      have := k.isLt
      omega)]
    exact payIn_hi a _ n L _ hge

/-- Stage 2: the top, docked. -/
theorem top_step {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (B1 : Fin (PT a) → List Bool)
    (hB : ∀ j : Fin (Ta a), B1 (topMap a j) = if j.val = 0 then PCJd4d1d9d7d1fa4313_Production.thrWord c else []) :
    ∃ A : Fin (Ta a) → List Bool,
      Step (RecoveryFocus.machine (topMap a) (PCJ6e421fabe2aa4155_SourceTopNative.machine a)) (topBudget a c)
        (fun _ => 0) B1 (fun _ => 0) (install (topMap a) B1 A) ∧
      A (PCJ6e421fabe2aa4155_SourceTopNative.slots a ((0 : Fin 2).natAdd (DecompositionSource.Counted.tapes a + 2))) =
        TopFront.payOf a c ∧ A ⟨0, by have := Ta_ge a; omega⟩ = PCJd4d1d9d7d1fa4313_Production.thrWord c := by
  obtain ⟨A, s2, hout, hA0⟩ := PCJ6e421fabe2aa4155_SourceTopNative.threshold_run a c
  have d2 := s2.dock (topMap a) (topMap_inj a) (fun _ => 0) B1 (fun _ => rfl) hB
  rw [dockH_existing (topMap a) (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at d2
  exact ⟨A, d2, hout, hA0⟩

/-- **One circuit's payload**: from the block's entry, `payOf a c` on `outTop a`, `thrWord c` on `1692`, the inputs
kept, every head at `0`. -/
theorem pay_step {n : ℕ} (c : NormalizedThresholdThresholdCircuit n) (L : ℕ) (hL : c.descriptionBits ≤ L) :
    ∃ out : Fin (PT a) → List Bool,
      Step (payM a) (ThrTab.thrBlockCost c L + 1 + topBudget a c) (fun _ => 0)
        (payIn a (encodeNormalizedThresholdThresholdCircuit c) n L) (fun _ => 0) out ∧
      out (outTop a) = TopFront.payOf a c ∧
      out ⟨1692, by show 1692 < 1781 + (Ta a - 1); omega⟩ = PCJd4d1d9d7d1fa4313_Production.thrWord c ∧
      out ⟨0, by show 0 < 1781 + (Ta a - 1); omega⟩ = frame (natWord (encodeNormalizedThresholdThresholdCircuit c)) ∧
      out ⟨1, by show 1 < 1781 + (Ta a - 1); omega⟩ = List.replicate n true ∧
      out ⟨2, by show 2 < 1781 + (Ta a - 1); omega⟩ = List.replicate L true := by
  obtain ⟨o1, s1, h0, h1, h2, -, h1692, -, -, -⟩ := ThrTab.thrBlock_step c L hL
  have d1 := blk_step a c L o1 s1
  obtain ⟨A, d2, hout, hA0⟩ := top_step a c _ (top_input a c L o1 h1692)
  refine ⟨_, d1.seq d2, ?_, ?_, ?_, ?_, ?_⟩
  · unfold outTop
    rw [install_slot _ (topMap_inj a)]
    exact hout
  · rw [← topMap_zero, install_slot _ (topMap_inj a)]
    exact hA0
  · rw [install_other _ _ _ _ (fun j => topMap_ne_low a j _ (by simp) (by simp))]
    rw [show (⟨0, by show 0 < 1781 + (Ta a - 1); omega⟩ : Fin (PT a)) = blkMap a 0 from rfl,
      install_slot _ (blkMap_inj a)]
    exact h0
  · rw [install_other _ _ _ _ (fun j => topMap_ne_low a j _ (by simp) (by simp))]
    rw [show (⟨1, by show 1 < 1781 + (Ta a - 1); omega⟩ : Fin (PT a)) = blkMap a 1 from rfl,
      install_slot _ (blkMap_inj a)]
    exact h1
  · rw [install_other _ _ _ _ (fun j => topMap_ne_low a j _ (by simp) (by simp))]
    rw [show (⟨2, by show 2 < 1781 + (Ta a - 1); omega⟩ : Fin (PT a)) = blkMap a 2 from rfl,
      install_slot _ (blkMap_inj a)]
    exact h2

end NearCubicWires.WireExponent3_5.PrimThrW.PayM
