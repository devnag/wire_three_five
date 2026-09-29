import Proof.Wire_3_5.Compiler.MachineC3aWord
import Proof.Wire_3_5.Primitive.Writers.C3WRun

/-! # C3 request writer, part 14: the call's fields

The compiler's fixed fields of the call's request (`C3ReqIface.preW`, `postW` at `r0`) are the writer's outputs:
the children table's entry count is the shape's label count (`sum_childTable`), the pool's records and the table's
entries are nonempty, the pool request is admissible for C3a′ (`poolReq_pre`: the halves fit the width, P3:1213-1215).

Paper quantities: the fields `preW`, `postW` of the call's request (P3:1886-1906, 1636-1664). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairRepresentation (natWord)

/-! ## The children table -/

theorem sum_getD_range {α : Type} : ∀ pool : List (List α),
    ((List.range pool.length).map fun a => (pool.getD a []).length).sum = pool.flatten.length
  | [] => rfl
  | x :: xs => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.flatten_cons,
      List.length_append]
    have e : ((fun a => ((x :: xs).getD a []).length) ∘ Nat.succ) = fun a => (xs.getD a []).length := by
      funext a; simp
    rw [e, sum_getD_range xs]
    simp

theorem sum_childTable (Q : ℕ) (pool : List (List SynEq)) :
    ((childTable Q pool).map List.length).sum = pool.flatten.length := by
  simp only [childTable, List.map_map, Function.comp_def, List.length_map, labelsOf, List.length_range']
  exact sum_getD_range pool

theorem childTable_ne (Q : ℕ) (pool : List (List SynEq)) : ∀ E ∈ childTable Q pool, ∀ y ∈ E, y ≠ [] := by
  intro E hE y hy e
  have := C3a.PO.childTable_entry Q pool E hE y hy
  rw [e] at this
  simp at this

theorem tableTape_eq (Es : List (List (List Bool))) : tableTape Es [] = atomsStream Es := by
  unfold tableTape atomsStream
  rw [List.append_nil]
  rfl

variable (a : RepairRepresentation.DecompositionAlgorithm)

theorem poolRecs_ne (h : ℕ) (hh : 1 ≤ h) {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool)
    (width : ℕ) (flips : List (List Bool)) : ∀ y ∈ poolRecs a h gates side width flips, y ≠ [] := by
  intro y hy e
  unfold poolRecs at hy
  obtain ⟨fe, _, hfe⟩ := List.mem_flatMap.mp hy
  have := denseRecs_width h side fe.1 width fe.2 y hfe
  rw [e] at this
  simp at this
  omega

/-! ## The halves fit the width -/

theorem filter_ofFn (g : ℕ → Bool) : ∀ n : ℕ,
    ((List.ofFn fun i : Fin n => g i).filter id).length = ((List.range n).filter g).length
  | 0 => rfl
  | n + 1 => by
    rw [List.ofFn_succ', List.range_succ, List.concat_eq_append, List.filter_append, List.filter_append,
      List.length_append, List.length_append]
    have ih := filter_ofFn g n
    simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [ih]
    by_cases hg : g n = true <;> simp [hg]

theorem count_interval (A B C : ℕ) (hAB : A ≤ B) (hBC : B ≤ C) : ∀ N : ℕ,
    ((List.range N).filter (fun x => decide (x < A ∨ (B ≤ x ∧ x < C)))).length = min N A + (min N C - min N B)
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_interval A B C hAB hBC N]
    by_cases hp : N < A ∨ (B ≤ N ∧ N < C)
    · simp only [List.filter_cons, List.filter_nil, decide_eq_true hp, if_true, List.length_singleton]
      rcases hp with hp | ⟨hp1, hp2⟩
      · rw [Nat.min_eq_left (show N ≤ A by omega), Nat.min_eq_left (show N + 1 ≤ A by omega),
          Nat.min_eq_left (show N ≤ C by omega), Nat.min_eq_left (show N + 1 ≤ C by omega),
          Nat.min_eq_left (show N ≤ B by omega), Nat.min_eq_left (show N + 1 ≤ B by omega)]
        omega
      · rw [Nat.min_eq_right (show A ≤ N by omega), Nat.min_eq_right (show A ≤ N + 1 by omega),
          Nat.min_eq_left (show N ≤ C by omega), Nat.min_eq_left (show N + 1 ≤ C by omega),
          Nat.min_eq_right (show B ≤ N by omega), Nat.min_eq_right (show B ≤ N + 1 by omega)]
        omega
    · simp only [List.filter_cons, List.filter_nil, decide_eq_false hp, Bool.false_eq_true, if_false,
        List.length_nil]
      have h1 : ¬ N < A := fun h => hp (Or.inl h)
      have h2 : B ≤ N → C ≤ N := fun hb => by
        by_contra hc
        exact hp (Or.inr ⟨hb, by omega⟩)
      by_cases hB : B ≤ N
      · have hC := h2 hB
        rw [Nat.min_eq_right (show A ≤ N by omega), Nat.min_eq_right (show A ≤ N + 1 by omega),
          Nat.min_eq_right (show C ≤ N by omega), Nat.min_eq_right (show C ≤ N + 1 by omega),
          Nat.min_eq_right (show B ≤ N by omega), Nat.min_eq_right (show B ≤ N + 1 by omega)]
        omega
      · rw [Nat.min_eq_right (show A ≤ N by omega), Nat.min_eq_right (show A ≤ N + 1 by omega),
          Nat.min_eq_left (show N ≤ C by omega), Nat.min_eq_left (show N + 1 ≤ C by omega),
          Nat.min_eq_left (show N ≤ B by omega), Nat.min_eq_left (show N + 1 ≤ B by omega)]
        omega

theorem side_getD (P : StarParams) (i : Fin P.n) :
    (PrimT.C4Geo.side P).getD i false = decide (i.val < P.r / 2 * P.b ∨
      (P.r * P.b ≤ i.val ∧ i.val < P.r * P.b + (P.n - P.r * P.b + 1) / 2)) := by
  simp [PrimT.C4Geo.side, List.getD_eq_getElem?_getD, StarParams.centerSide]

theorem nLeft_eq (P : StarParams) : nLeft (PrimT.C4Geo.side P) P.n = PrimT.C4Geo.width P := by
  have hr := P.r_mul_b_le
  have hh := P.r_half_add
  have e1 : P.r / 2 * P.b ≤ P.r * P.b := Nat.mul_le_mul_right _ (by omega)
  unfold nLeft
  have e3 : ((List.ofFn fun i : Fin P.n => (PrimT.C4Geo.side P).getD i false).filter id).length =
      ((List.range P.n).filter (fun x => decide (x < P.r / 2 * P.b ∨
        (P.r * P.b ≤ x ∧ x < P.r * P.b + (P.n - P.r * P.b + 1) / 2)))).length := by
    have := filter_ofFn (fun x => decide (x < P.r / 2 * P.b ∨
        (P.r * P.b ≤ x ∧ x < P.r * P.b + (P.n - P.r * P.b + 1) / 2))) P.n
    have e : (fun i : Fin P.n => (PrimT.C4Geo.side P).getD i false) = (fun i : Fin P.n => decide (i.val < P.r / 2 * P.b ∨
        (P.r * P.b ≤ i.val ∧ i.val < P.r * P.b + (P.n - P.r * P.b + 1) / 2))) := funext (side_getD P)
    rw [← this, e]
  rw [e3, count_interval _ _ _ e1 (by omega)]
  unfold PrimT.C4Geo.width PrimT.C4Geo.hL
  rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
  omega

theorem nRight_le (P : StarParams) : nRight (PrimT.C4Geo.side P) P.n ≤ PrimT.C4Geo.width P := by
  have hL := nLeft_eq P
  unfold nLeft at hL
  unfold nRight
  have e := List.length_eq_length_filter_add (l := List.ofFn fun i : Fin P.n => (PrimT.C4Geo.side P).getD i false) id
  simp only [List.length_ofFn] at e
  have e' : (List.filter (fun b => !id b) (List.ofFn fun i : Fin P.n => (PrimT.C4Geo.side P).getD i false)) =
      List.filter (fun b => !b) (List.ofFn fun i : Fin P.n => (PrimT.C4Geo.side P).getD i false) := rfl
  rw [e'] at e
  have hr := P.r_mul_b_le
  have hh := P.r_half_add
  have e1 : P.r / 2 * P.b + P.r / 2 * P.b = P.r * P.b := by rw [← add_mul, hh]
  unfold PrimT.C4Geo.width PrimT.C4Geo.hL at hL ⊢
  omega

/-- **The call's pool request is admissible for C3a′** (`PoolReq.Pre`). -/
theorem poolReq_pre (P : StarParams) (σ : P.Translation) (gates : List (NormalizedThresholdGate P.n))
    (h Q psi : ℕ) : (PrimT.C4Geo.poolReq P σ gates h Q psi).Pre := by
  refine ⟨by simp [PrimT.C4Geo.poolReq, PrimT.C4Geo.side], ?_, ?_, ?_⟩
  · intro f hf
    simp only [PrimT.C4Geo.poolReq, PrimT.C4Geo.flips, List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    simp only [List.length_ofFn]
    rfl
  · show nLeft (PrimT.C4Geo.side P) P.n ≤ PrimT.C4Geo.width P
    rw [nLeft_eq]
  · exact nRight_le P

end NearCubicWires.WireExponent3_5.PrimAsm.C3Field
