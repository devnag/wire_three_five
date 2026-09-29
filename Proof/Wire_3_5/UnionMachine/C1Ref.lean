import Proof.Wire_3_5.UnionMachine.C1Gates
import Proof.Wire_3_5.UnionMachine.C1Asm
import Proof.Wire_3_5.UnionMachine.FrontSelReq
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
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- The PCPP variables' count. -/
abbrev VG : ℕ := g.pcpp.systematicBits + g.pcpp.auxiliaryBits

/-- The guess's carriers by index. -/
def CsG (x : ℕ) : Stars.Carrier g.q := if h : x < VG g then g.carrier ⟨x, h⟩ else []

/-- The PCPP output's literal list (`pcppOutput`'s last field). -/
def litsG : List ℕ :=
  FrontTW.pairsOf (fun i : Fin (2 ^ g.pcpp.clauseBits) => RepairRepresentation.literalIndex (g.pcpp.clauses i).left)
    (fun i => RepairRepresentation.literalIndex (g.pcpp.clauses i).right)

theorem countP_pairsOf {M : ℕ} (a b : Fin M → ℕ) (p : ℕ → Bool) :
    (FrontTW.pairsOf a b).countP p = ∑ i : Fin M, ((if p (a i) then 1 else 0) + (if p (b i) then 1 else 0)) := by
  unfold FrontTW.pairsOf
  rw [List.countP_flatMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [List.countP_cons]; omega

theorem cnt_eq (X : PcppVar g.pcpp) :
    C1Cnt.cntOf X.val (litsG g) =
      (Finset.univ.filter fun p : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 => posVar g.pcpp p.1 p.2 = X).card := by
  unfold C1Cnt.cntOf litsG
  rw [← List.countP_eq_length_filter, countP_pairsOf, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [posVar_zero, posVar_one, FrontTW.litIdx_div, decide_eq_true_eq]
  congr 1
  · by_cases h : ComponentwiseBranchExtraction.literalIndex (g.pcpp.clauses i).left = X
    · simp [h]
    · have : (ComponentwiseBranchExtraction.literalIndex (g.pcpp.clauses i).left).val ≠ X.val :=
        fun e => h (Fin.ext e)
      simp [h, this]
  · by_cases h : ComponentwiseBranchExtraction.literalIndex (g.pcpp.clauses i).right = X
    · simp [h]
    · have : (ComponentwiseBranchExtraction.literalIndex (g.pcpp.clauses i).right).val ≠ X.val :=
        fun e => h (Fin.ext e)
      simp [h, this]

theorem weight_eq (X : PcppVar g.pcpp) :
    g.weight X = (C1Cnt.cntOf X.val (litsG g) : ℚ) / 2 ^ (g.pcpp.clauseBits + 1) := by
  unfold UnionGuess.weight
  rw [cnt_eq, pow_succ]
  ring

theorem pos_iff (X : PcppVar g.pcpp) : pos (litsG g) X.val ↔ g.weight X ≠ 0 := by
  rw [weight_eq]
  unfold pos
  have h2 : (0 : ℚ) < 2 ^ (g.pcpp.clauseBits + 1) := by positivity
  constructor
  · intro h; exact div_ne_zero (by exact_mod_cast (Nat.pos_iff_ne_zero.mp h)) h2.ne'
  · intro h
    rcases Nat.eq_zero_or_pos (C1Cnt.cntOf X.val (litsG g)) with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0

theorem vsN_eq : vsN (litsG g) (VG g) = (FrontSelReq.vsPos g).map Fin.val := by
  unfold vsN FrontSelReq.vsPos
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  congr 1
  apply List.filter_congr
  intro X _
  simp only [Function.comp, decide_eq_decide]
  exact pos_iff g X

theorem CsG_val (X : PcppVar g.pcpp) : CsG g X.val = g.carrier X := by
  unfold CsG; rw [dif_pos X.isLt]

end Guess

section Req
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

theorem segStart_eq (i : ℕ) :
    FrontSelReq.segStart (CsG g) (vsN (litsG g) (VG g)) i = FrontSelReq.segStart g.carrier (FrontSelReq.vsPos g) i := by
  unfold FrontSelReq.segStart
  rw [vsN_eq, ← List.map_take, List.map_map]
  congr 1
  apply List.map_congr_left
  intro X _
  simp [CsG_val]

theorem popsW_eq :
    popsW (CsG g) (fun x => ((C1Cnt.cntOf x (litsG g) : ℚ) / 2 ^ (g.pcpp.clauseBits + 1))) (vsN (litsG g) (VG g)) =
      ((FrontSelReq.selReqOf g).pops).flatMap fun X => natListWord X.1 ++ NearCubicWires.WireExponent3_5.ratWord X.2 := by
  unfold popsW FrontSelReq.selReqOf FrontSelReq.selReqOn
  simp only
  rw [List.mapIdx_eq_ofFn, List.ofFn_eq_map, List.flatMap_map]
  have hl : (vsN (litsG g) (VG g)).length = (FrontSelReq.vsPos g).length := by rw [vsN_eq, List.length_map]
  rw [hl, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  have hget : (vsN (litsG g) (VG g)).getD i.val 0 = ((FrontSelReq.vsPos g).get i).val := by
    rw [vsN_eq, List.getD_eq_getElem _ _ (by simp), List.getElem_map]; rfl
  rw [hget, segStart_eq, CsG_val, ← weight_eq]

/-- **The loop's pieces are C1's request.** -/
theorem reqWord_selWord (cr : ℕ) (hr : B.rOf g.q = Ledger.rowBr cr g.q) :
    C1Asm.reqWord g.q (Ledger.rowBr cr g.q) (gtF (CsG g) (litsG g) (VG g)) (npF (litsG g) (VG g))
        (GF (CsG g) (litsG g) (VG g)) (PF (CsG g) (litsG g) g.pcpp.clauseBits (VG g)) =
      Plan.selWord (FrontSelReq.selReqOf g) := by
  rw [PF_eq, popsW_eq, GF_eq, gtF_eq, npF_eq, vsN_eq]
  unfold C1Asm.reqWord Plan.selWord
  have hL : (((FrontSelReq.vsPos g).map Fin.val).map (fun x => (CsG g x).length)).sum =
      (FrontSelReq.selReqOf g).gates.length := by
    show _ = (((FrontSelReq.vsPos g).flatMap g.carrier).map FrontSelReq.toInt).length
    rw [List.length_map, List.map_map, List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro X _
    simp [CsG_val]
  have hF : ((FrontSelReq.vsPos g).map Fin.val).flatMap (fun x => (CsG g x).flatMap GateConv.selGate) =
      (FrontSelReq.selReqOf g).gates.flatMap
        (fun G => (List.ofFn fun i => RepairRepresentation.intWord (G.weights i)).flatten ++
          RepairRepresentation.intWord G.threshold) := by
    show _ = (((FrontSelReq.vsPos g).flatMap g.carrier).map FrontSelReq.toInt).flatMap _
    calc ((FrontSelReq.vsPos g).map Fin.val).flatMap (fun x => (CsG g x).flatMap GateConv.selGate)
        = ((FrontSelReq.vsPos g).flatMap g.carrier).flatMap GateConv.selGate := by
          rw [List.flatMap_map, List.flatMap_assoc]
          apply List.flatMap_congr
          intro X _
          simp [CsG_val]
      _ = _ := (GateConv.selGates_selWord _).symm
  have hP : ((FrontSelReq.vsPos g).map Fin.val).length = (FrontSelReq.selReqOf g).pops.length := by
    simp [FrontSelReq.selReqOf, FrontSelReq.selReqOn]
  rw [hL, hF, hP, ← hr]
  rfl

end Req

end NearCubicWires.WireExponent3_5.UnionMachine.C1Ref
