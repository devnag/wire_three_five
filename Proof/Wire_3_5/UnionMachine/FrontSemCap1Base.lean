import Proof.Wire_3_5.UnionMachine.FrontSemGate
import Proof.Wire_3_5.UnionMachine.FrontSemPathBase

/-! # C6 front, the semantic core (12): a guess's size envelope and its call table (P3:3485-3491, 3669-3691)

**`GEnv g Λ K`**: every size of the guess `g` the front's capacities read is at most `K` (the width, the variable
count, `2^{cb}`, the grid, the mass, the PCPP size bound, the atoms' and the carriers' codes, the translation).
From it: every scheduled call's request word (**`word_le`**, PA's `word_length`), every entry word, and the call
table's words (**`twWords_le`**: the schedule's length, `length_schedule_le`, times an entry's length).

Paper quantity of the main types: the guess's call table (its requests and coefficients) against the width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (twWords)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)

theorem natWord_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := PrimAsm.CallSize.natWord_len_le_self x

theorem natWord_bits (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := Bindings.Williams14.natWord_length x

theorem frame_len (w : List Bool) : (RepairOrdinary.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => show (true :: b :: RepairOrdinary.frame w).length = _; simp only [List.length_cons, ih]; ring

theorem flatMap_le {α β : Type} (l : List α) (f : α → List β) (k : ℕ) (h : ∀ x ∈ l, (f x).length ≤ k) :
    (l.flatMap f).length ≤ l.length * k := PrimAsm.CallSize.flatMap_length_le l f k h

section Env
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N}

/-- **A tuple request's word.** -/
theorem word_le (m : Mode) (q : ℕ) {α : Type} (circ : α → m.Circuit q) (t : Fin 4 → α) (cs : List (Stars.Carrier q))
    (tr : List ℕ) (K : ℕ) (hc : ∀ k, (natWord (m.code (circ (t k)))).length ≤ K) (hcs : cs.length ≤ 2)
    (hcar : ∀ X ∈ cs, natBitLength (Stars.Carrier.code X) ≤ K) (htr : (natListWord tr).length ≤ K) :
    (tupleRequest m q circ t cs tr).word.length ≤ 2 * q + 9 * K + 24 := by
  rw [PrimAsm.Codec.word_length]
  have h1 := natWord_le q
  have h2 : (natWord 4).length ≤ 11 := natWord_le 4
  have h3 : ((PrimAsm.Codec.codeList (tupleRequest m q circ t cs tr)).flatMap natWord).length ≤ 4 * K := by
    have := flatMap_le (PrimAsm.Codec.codeList (tupleRequest m q circ t cs tr)) natWord K (fun c hc' => by
      unfold PrimAsm.Codec.codeList at hc'
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc'
      exact hc i)
    rwa [PrimAsm.Codec.codeList, List.length_ofFn] at this
  have h4 : (natListWord (PrimAsm.Codec.carrierCodes (tupleRequest m q circ t cs tr))).length ≤ 4 * K + 9 := by
    unfold natListWord PrimAsm.Codec.carrierCodes
    rw [List.length_append, List.length_map]
    have e1 := natWord_le cs.length
    have e2 := flatMap_le (cs.map Stars.Carrier.code) natWord (2 * K + 1) (fun c hc' => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc'
      rw [natWord_bits]; have := hcar X hX; omega)
    rw [List.length_map] at e2
    have e3 : cs.length * (2 * K + 1) ≤ 2 * (2 * K + 1) := Nat.mul_le_mul_right _ hcs
    show (natWord (tupleRequest m q circ t cs tr).carriers.length).length +
      ((tupleRequest m q circ t cs tr).carriers.map Stars.Carrier.code |>.flatMap natWord).length ≤ _
    show (natWord cs.length).length + ((cs.map Stars.Carrier.code).flatMap natWord).length ≤ _
    omega
  have h5 : (natListWord (tupleRequest m q circ t cs tr).translation).length ≤ K := htr
  show (natWord q).length + 1 + (natWord 4).length + _ + _ + _ ≤ _
  omega

variable {Λ K : ℕ}

/-- An entry word's length bound. -/
def EW (K : ℕ) : ℕ := 2 * (K + K) ^ 4 + 22 * K + 54

/-- The call count bound. -/
def CN (K : ℕ) : ℕ := 24 * K * (1 + 2 * K * (K + 1)) ^ 4

end Env

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1
