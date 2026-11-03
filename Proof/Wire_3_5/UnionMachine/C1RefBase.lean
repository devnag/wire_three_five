import Proof.Wire_3_5.UnionMachine.C1Gates
import Proof.Wire_3_5.UnionMachine.C1Asm
import Proof.Wire_3_5.UnionMachine.FrontSelReqBase
import Proof.Wire_3_5.UnionMachine.FrontTWBridge3

/-! # C6 front, the C1 dock: the loop's pieces are C1's request (P3:1326-1330, 3395-3399, 3673)

The carrier loop leaves the positive-count variables' gates `GF V`, populations `PF V`, gate total `gtF V` and count
`npF V`; with the PCPP output's literal list (`litsG g`: `2i`, `2i+1` per clause position) and the carriers of the guess
(`CsG g`), they are exactly the pieces of `Plan.selWord (FrontSelReq.selReqOf g)`:
* `vsN j` (the positive-count variables below `j`), the pieces as lists over `vsN j` (`GF_eq`, `gtF_eq`, `npF_eq`,
  `PF_eq`);
* `cnt_eq` (the count is the incidence count), `weight_eq` (`p_X = c_X/2^{cb+1}`), `pos_iff`;
* **`reqWord_selWord`**: `C1Asm.reqWord q (rowBr cr q) (gtF V) (npF V) (GF V) (PF V) = Plan.selWord (selReqOf g)`.

Paper quantity of the main type: `star:selection`'s request at the union's weighted carriers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Ref
open NearCubicWires NearCubicWires.WireExponent3_5.UnionMachine.C1Gates
open NearCubicWires.RepairRepresentation (natWord natListWord)

section Lists
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb : ℕ)

/-- The positive-count variables below `j`. -/
def vsN (j : ℕ) : List ℕ := (List.range j).filter fun x => decide (pos lits x)

theorem vsN_succ (j : ℕ) : vsN lits (j + 1) = vsN lits j ++ if pos lits j then [j] else [] := by
  unfold vsN; rw [List.range_succ, List.filter_append]
  by_cases h : pos lits j <;> simp [h]

theorem GF_eq (j : ℕ) : GF Cs lits j = (vsN lits j).flatMap fun x => (Cs x).flatMap GateConv.selGate := by
  induction j with
  | zero => rfl
  | succ j ih => rw [GF, ih, vsN_succ]; by_cases h : pos lits j <;> simp [h]

theorem gtF_eq (j : ℕ) : gtF Cs lits j = ((vsN lits j).map fun x => (Cs x).length).sum := by
  induction j with
  | zero => rfl
  | succ j ih => rw [gtF, ih, vsN_succ]; by_cases h : pos lits j <;> simp [h]

theorem npF_eq (j : ℕ) : npF lits j = (vsN lits j).length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [npF, ih, vsN_succ]; by_cases h : pos lits j <;> simp [h]

/-- The populations over a list of variables. -/
def popsW (w : ℕ → ℚ) (vs : List ℕ) : List Bool :=
  (List.range vs.length).flatMap fun i =>
    natListWord (List.range' (FrontSelReq.segStart Cs vs i) (Cs (vs.getD i 0)).length) ++
      NearCubicWires.WireExponent3_5.ratWord (w (vs.getD i 0))

theorem segStart_append (vs : List ℕ) (y : List ℕ) (i : ℕ) (hi : i ≤ vs.length) :
    FrontSelReq.segStart Cs (vs ++ y) i = FrontSelReq.segStart Cs vs i := by
  unfold FrontSelReq.segStart; rw [List.take_append_of_le_length hi]

theorem segStart_len (vs : List ℕ) : FrontSelReq.segStart Cs vs vs.length = (vs.map fun x => (Cs x).length).sum := by
  unfold FrontSelReq.segStart; rw [List.take_length]

theorem popsW_snoc (w : ℕ → ℚ) (vs : List ℕ) (x : ℕ) :
    popsW Cs w (vs ++ [x]) = popsW Cs w vs ++ (natListWord (List.range' ((vs.map fun x => (Cs x).length).sum)
      (Cs x).length) ++ NearCubicWires.WireExponent3_5.ratWord (w x)) := by
  unfold popsW
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append]
  congr 1
  · apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [segStart_append Cs vs [x] i hi.le, List.getD_append _ _ _ _ hi]
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [segStart_append Cs vs [x] vs.length le_rfl, segStart_len, List.getD_append_right _ _ _ _ le_rfl]
    simp

theorem PF_eq (j : ℕ) :
    PF Cs lits cb j = popsW Cs (fun x => ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1))) (vsN lits j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [PF, ih, vsN_succ]
    by_cases h : pos lits j
    · simp only [h, if_true]
      rw [popsW_snoc, ← gtF_eq]
    · simp [h]

end Lists

/-! ## The guess -/

section Guess
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N} 

theorem countP_pairsOf {M : ℕ} (a b : Fin M → ℕ) (p : ℕ → Bool) :
    (FrontTW.pairsOf a b).countP p = ∑ i : Fin M, ((if p (a i) then 1 else 0) + (if p (b i) then 1 else 0)) := by
  unfold FrontTW.pairsOf
  rw [List.countP_flatMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [List.countP_cons]; omega

end Guess

section Req
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost

end Req

end NearCubicWires.WireExponent3_5.UnionMachine.C1Ref
