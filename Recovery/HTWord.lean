import CheckedPCPP.H2Poly
import CheckedPCPP.ChecksW
import CheckedPCPP.PolyClass
import CheckedPCPP.Composite
import Outer.Size

/-!
# Length bounds for the Case 2 producer's words ((a′) form)

The producer's cost (the near-cubic-gates paper's uniform recovery: "computable in polynomial time once the oracle is known") is charged on the
lengths of its input words. Two of them are new with the repair:
* the word of `C_{⟨B_src⟩_ν}` (`OracleOutput.word`, imp:short-pcp): `word_len_le` bounds it by the size of `C` and its
  arity `ℓ`; `mwWord_poly`: at the instance `⟨B_src⟩_ν` it is at most a fixed polynomial in `2^ν` (the import's size
  clause `|C| ≤ K (L_ν + |bin T_G(L_ν)| + 1)^e`, `Outer.outC_size_le`, and `ℓ ≤ q(N_ν)`, `Outer.ell_le_width`);
* the native descriptor of a Boolean circuit (`desc_len_le'`, quadratic in its size and arity; the same bound as the
  composite's `Comp.desc_len_le`, restated here so that the producer does not depend on the composite's internals).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.MW20 NearCubicGates.Close NearCubicGates.Close.CheckedPCPP

/-! ## The word of an oracle circuit -/

theorem natWord_le (x M : ℕ) (h : x ≤ M) : (natWord x).length ≤ 2 * M + 3 :=
  (H2Poly.natWord_len_le x).trans (by omega)

theorem flatMap_len_le {α β : Type} (f : α → List β) (K : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).length ≤ K) → (l.flatMap f).length ≤ l.length * K
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := flatMap_len_le f K l (fun b hb => h b (List.mem_cons_of_mem a hb))
    nlinarith

/-- The word of a well-formed node at index `idx` has at most `ℓ + 3` numbers, each at most `idx + n + 5`. -/
theorem oracleNodeWord_len_le {n a : ℕ} (nd : OracleNode n a) (idx M : ℕ) (h : nd.WellFormedAt idx)
    (hM : idx + n + 5 ≤ M) : (oracleNodeWord nd).length ≤ (a + 3) * (2 * M + 3) := by
  have hA : 3 * (2 * M + 3) ≤ (a + 3) * (2 * M + 3) := Nat.mul_le_mul_right _ (by omega)
  cases nd with
  | const v =>
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 0 M (by omega)
    have := natWord_le v.toNat M (by have := Bool.toNat_le v; omega)
    omega
  | input i =>
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 1 M (by omega)
    have := natWord_le i.val M (by have := i.isLt; omega)
    have := natWord_le 0 M (by omega)
    omega
  | not c =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 2 M (by omega)
    have := natWord_le c M (by omega)
    have := natWord_le 0 M (by omega)
    omega
  | and l r =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 3 M (by omega)
    have := natWord_le l M (by omega)
    have := natWord_le r M (by omega)
    omega
  | or l r =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have := natWord_le 4 M (by omega)
    have := natWord_le l M (by omega)
    have := natWord_le r M (by omega)
    omega
  | oracle args =>
    simp only [OracleNode.WellFormedAt] at h
    simp only [oracleNodeWord, List.length_append]
    have h5 := natWord_le 5 M (by omega)
    have hf : ((List.ofFn fun j => natWord (args j)).flatten).length ≤ a * (2 * M + 3) := by
      rw [List.length_flatten]
      have := List.sum_le_card_nsmul ((List.ofFn fun j => natWord (args j)).map List.length) (2 * M + 3) (by
        intro x hx
        simp only [List.mem_map, List.mem_ofFn] at hx
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hx
        exact natWord_le _ M (by have := h j; omega))
      simpa using this
    nlinarith

/-- **The word of an oracle circuit** has length at most `(S + 3)(ℓ + 3)(2(S + ℓ + 5) + 3)` (`S` its size). -/
theorem word_len_le (o : OracleOutput) :
    o.word.length ≤ (o.circuit.size + 3) * ((o.ell + 3) * (2 * (o.circuit.size + o.ell + 5) + 3)) := by
  set S := o.circuit.size with hS
  set M := S + o.ell + 5 with hM
  have hn : ∀ nd ∈ o.circuit.nodes, (oracleNodeWord nd).length ≤ (o.ell + 3) * (2 * M + 3) := by
    intro nd hnd
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hnd
    have hw := o.circuit.wellFormed idx
    rw [hidx] at hw
    have : idx.val < S := idx.isLt
    exact oracleNodeWord_len_le nd idx.val M hw (by omega)
  have hb := flatMap_len_le oracleNodeWord _ o.circuit.nodes hn
  have h1 := natWord_le o.ell M (by omega)
  have h2 := natWord_le o.circuit.nodes.length M (by change S ≤ M; omega)
  have h3 := natWord_le o.circuit.output.val M (by have := o.circuit.output.isLt; change _ < S at this; omega)
  have hl : o.circuit.nodes.length = S := rfl
  unfold OracleOutput.word
  simp only [List.length_append]
  rw [hl] at hb
  have hA : 2 * M + 3 ≤ (o.ell + 3) * (2 * M + 3) := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

/-! ## The native descriptor of a Boolean circuit -/

theorem fields_le_of_wf' {n : ℕ} (nd : BooleanNode n) (idx : ℕ) (h : nd.WellFormedAt idx) (j : Fin 3) :
    PCPPRequestNodeSchema.fields nd j ≤ idx + n + 4 := by
  cases nd with
  | const b =>
    have := Bool.toNat_le b
    fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | input i => fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | not c => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | and l r => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)
  | or l r => simp [BooleanNode.WellFormedAt] at h; fin_cases j <;> (simp [PCPPRequestNodeSchema.fields]; try omega)

/-- The native descriptor of a circuit is at most quadratic in its size and arity. -/
theorem desc_len_le' {n : ℕ} (c : BooleanCircuit n) :
    (PCPPNative.descriptor c).length ≤ (c.size + 1) * (6 * (c.size + n + 4) + 9) + 2 * n + 4 * c.size + 9 := by
  rw [PCPPNative.descriptor_eq]
  have hf : ∀ nd ∈ c.nodes, ∀ j, PCPPRequestNodeSchema.fields nd j ≤ c.size + n + 4 := by
    intro nd hnd j
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hnd
    have hw := c.wellFormed idx
    rw [hidx] at hw
    have := fields_le_of_wf' nd idx.val hw j
    have : idx.val < c.size := idx.isLt
    omega
  have hb := ChecksW.flatMap_native_le (c.size + n + 4) c.nodes hf
  have h1 := H2Poly.natWord_len_le n
  have h2 := H2Poly.natWord_len_le c.nodes.length
  have h3 := H2Poly.natWord_len_le c.output.val
  have ho := c.output.isLt
  have hs : c.size = c.nodes.length := rfl
  simp only [List.length_append]
  change c.output.val < c.size at ho
  nlinarith

/-! ## The word of `C_{⟨B_src⟩_ν}` is polynomial in `2^ν` -/

end NearCubicGates.Close.Recovery.HT
