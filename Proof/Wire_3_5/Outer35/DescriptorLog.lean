import Proof.PCP.PCPPNativeRequestSchema
import Proof.PCP.PCPPRequestNodeSchema
import Proof.Wire_3_5.Front35.Pair

/-!
# The description of a circuit has `O(size · log size)` bits

Paper v2, §H.6: "Such a description has at most `c_fmt(s'+1)log₂(s'+a'+2)` bits"; Lemma H.7(a): "the description of
`Γ_src` has fewer than `λ_a` bits". The description is proof 1's native descriptor
`natWord n ++ natWord |nodes| ++ native nodes ++ natWord output`; every node writes three framed fields, each at most
`n + index + 4` (`PCPPRequestNodeSchema.field_bound`), so each field has `O(log (n + size))` bits.

**`descriptor_length_le_log`**: `|descriptor c| ≤ 6 (|c| + 1)(natBitLength (n + |c| + 4) + 1)`.

Paper quantity: the description length of a circuit (the `λ_a` guard's left side).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Outer35

open _root_.NearCubicWires _root_.NearCubicWires.RepairRepresentation _root_.NearCubicWires.RepairOrdinary

theorem natBitLength_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  omega

theorem flatMap_length_le {α β : Type} (l : List α) (f : α → List β) (K : ℕ) (h : ∀ x ∈ l, (f x).length ≤ K) :
    (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.add_mul, one_mul]
    omega

/-- One node writes three framed fields, each at most `n + index + 4`. -/
theorem native_length_le {n : ℕ} (node : BooleanNode n) (index M : ℕ) (hwf : node.WellFormedAt index)
    (hM : n + index + 4 ≤ M) :
    (PCPPRequestNodeSchema.native node).length ≤ 3 * (2 * natBitLength M + 1) := by
  unfold PCPPRequestNodeSchema.native
  simp only [List.length_append, NearCubicWires.WireExponent3_5.UnionMachine.Front35.natWord_length]
  have h0 := natBitLength_mono ((PCPPRequestNodeSchema.field_bound node index hwf 0).trans hM)
  have h1 := natBitLength_mono ((PCPPRequestNodeSchema.field_bound node index hwf 1).trans hM)
  have h2 := natBitLength_mono ((PCPPRequestNodeSchema.field_bound node index hwf 2).trans hM)
  omega

/-- **The description has `O(size · log size)` bits** (§H.6; the quadratic `descriptor_length_bound` is not enough
for `λ_a = a^{G+1}`). -/
theorem descriptor_length_le_log {n : ℕ} (c : BooleanCircuit n) :
    (PCPPNative.descriptor c).length ≤ 6 * (c.size + 1) * (natBitLength (n + c.size + 4) + 1) := by
  set M := n + c.size + 4 with hM
  rw [PCPPNative.descriptor_eq]
  have hnodes : (c.nodes.flatMap PCPPRequestNodeSchema.native).length ≤ c.nodes.length * (3 * (2 * natBitLength M + 1)) := by
    refine flatMap_length_le _ _ _ (fun x hx => ?_)
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hx
    refine native_length_le _ i.val M (c.wellFormed i) ?_
    have := i.isLt
    have : c.nodes.length = c.size := rfl
    omega
  have hs : c.nodes.length = c.size := rfl
  have e1 := natBitLength_mono (show n ≤ M by omega)
  have e2 := natBitLength_mono (show c.nodes.length ≤ M by omega)
  have e3 := natBitLength_mono (show c.output.val ≤ M by have := c.output.isLt; omega)
  simp only [List.length_append, NearCubicWires.WireExponent3_5.UnionMachine.Front35.natWord_length]
  rw [hs] at hnodes
  have key : 3 * (2 * natBitLength M + 1) + c.size * (3 * (2 * natBitLength M + 1)) ≤
      6 * (c.size + 1) * (natBitLength M + 1) := by nlinarith
  omega

end NearCubicWires.WireExponent3_5.Outer35
