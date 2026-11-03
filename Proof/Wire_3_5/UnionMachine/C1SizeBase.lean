import Proof.Wire_3_5.UnionMachine.C1RefBase

/-! # C6 front, the C1 dock: the size of C1's request (C1's `c1sized` precondition; P3:1335, 3669-3671)

C1's contract `c1sized d` takes requests with `|selWord R| ≤ (R.n+1)^d`. At the union's request `selReqOf g` every
piece is bounded by one number `M` dominating `q`, the variables' count, the grid size, every atom's and parity's
description bits, `2^{cb+1}` and `r`:
* `gates_len_le` (a circuit charges at most its description bits' many gates), `gate_enc_le` (each charged gate's
  encoding bits are at most the circuit's description bits), `selGate_len` (`|selGate g| = 2·encodingBits + 2q + 2`);
* `carrier_len`, `carrier_enc`;
* **`selWord_len_le`**: `|selWord (selReqOf g)| ≤ 100·M^6`.

Paper quantity of the main type: the length of `star:selection`'s request at the union's weighted carriers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Size
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord intWord)

/-! ## Lists -/

theorem len_flatMap_le {α β : Type} (l : List α) (f : α → List β) (B : ℕ) (h : ∀ a ∈ l, (f a).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

theorem len_flatten_le {β : Type} (L : List (List β)) (B : ℕ) (h : ∀ l ∈ L, l.length ≤ B) :
    L.flatten.length ≤ L.length * B := by
  have e : L.flatten = L.flatMap id := by simp
  rw [e]
  exact len_flatMap_le L id B h

/-! ## Circuits -/

theorem gates_len_le (m : Mode) {n : ℕ} (C : m.Circuit n) : (m.gates C).length ≤ m.descriptionBits C := by
  cases m
  · show (Stars.thrGates C).length ≤ C.top.descriptionBits + ∑ j, (C.bottom j).descriptionBits
    have h1 : C.bottomCount ≤ C.top.descriptionBits := by
      unfold SupportedNormalizedGate.descriptionBits; omega
    unfold Stars.thrGates
    rw [List.length_map]
    have h2 := List.length_filter_le (fun i => decide (i ∈ C.top.support)) (List.finRange C.bottomCount)
    rw [List.length_finRange] at h2
    omega
  · show (Stars.symGates C).length ≤ C.bottomCount + 1 + ∑ j, (C.bottom j).descriptionBits
    unfold Stars.symGates
    rw [List.length_map, List.length_finRange]
    omega

theorem gate_enc_le (m : Mode) {n : ℕ} (C : m.Circuit n) :
    ∀ g ∈ m.gates C, g.encodingBits ≤ m.descriptionBits C := by
  cases m
  · intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    show (C.bottom i).gate.encodingBits ≤ C.top.descriptionBits + ∑ j, (C.bottom j).descriptionBits
    have h1 : (C.bottom i).gate.encodingBits ≤ (C.bottom i).descriptionBits := Nat.le_add_right _ _
    have h2 : (C.bottom i).descriptionBits ≤ ∑ j, (C.bottom j).descriptionBits :=
      Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  · intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    show (C.bottom i).gate.encodingBits ≤ C.bottomCount + 1 + ∑ j, (C.bottom j).descriptionBits
    have h1 : (C.bottom i).gate.encodingBits ≤ (C.bottom i).descriptionBits := Nat.le_add_right _ _
    have h2 : (C.bottom i).descriptionBits ≤ ∑ j, (C.bottom j).descriptionBits :=
      Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega

theorem selGate_len {q : ℕ} (g : NormalizedThresholdGate q) :
    (GateConv.selGate g).length = 2 * g.encodingBits + 2 * q + 2 := by
  unfold GateConv.selGate NormalizedThresholdGate.encodingBits
  rw [List.length_append, List.length_flatMap, GateConv.intWord_len', List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp, GateConv.intWord_len', intBitLength]
  simp only [natBitLength, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_add]
  ring

/-! ## Carriers -/

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} (M : ℕ)

theorem segStart_le {α β : Type} (f : α → List β) (l : List α) (i : ℕ) :
    FrontSelReq.segStart f l i ≤ (l.flatMap f).length := by
  unfold FrontSelReq.segStart
  rw [List.length_flatMap]
  have e : l.map (fun a => (f a).length) = (l.take i).map (fun a => (f a).length) ++
      (l.drop i).map (fun a => (f a).length) := by
    rw [← List.map_append, List.take_append_drop]
  rw [e, List.sum_append]
  omega

theorem nw_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  rw [PrimAsm.ParseNat.natWord_length]
  have := PrimAsm.CopyNat.natBitLength_le_self_succ x
  omega

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.C1Size
