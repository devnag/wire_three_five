import Proof.Wire_3_5.UnionMachine.FrontTWBridge2

/-! # C6 front, U5: the table writer's three passes are the tests' term lists (P3:3685-3691, 3483-3489)

The PCPP output's literal list is `literalIndex` of each clause's two literals (base `pcppOutput`): the literal index
of `±x_i` is `2i` or `2i + 1`, so `⌊ℓ/2⌋` is the position's variable and `ℓ mod 2` its sign (**`litIdx_div`**,
**`litIdx_mod`**). Clause by clause, the table writer's pass outputs are the machine-order term lists' entries:
**`accW_V_eq`**, **`accW_Q_eq`**, **`accW_Mu_eq`** (`FrontTableRef.myV/myQ/myMu`).

Paper quantity of the main statements: the call table of `(tr:tests)`, test by test. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge (entryOf)

/-! ## Literal indices -/

theorem litIdx_div {n : ℕ} (l : Literal n) :
    RepairRepresentation.literalIndex l / 2 = (ComponentwiseBranchExtraction.literalIndex l).val := by
  cases l <;> simp [RepairRepresentation.literalIndex, ComponentwiseBranchExtraction.literalIndex] <;> omega

theorem litIdx_mod {n : ℕ} (l : Literal n) :
    RepairRepresentation.literalIndex l % 2 = if ComponentwiseBranchExtraction.literalNegated l then 1 else 0 := by
  cases l <;> simp [RepairRepresentation.literalIndex, ComponentwiseBranchExtraction.literalNegated] <;> omega

/-! ## The literal list -/

/-- A list of pairs, flattened. -/
def pairsOf {M : ℕ} (a b : Fin M → ℕ) : List ℕ := (List.finRange M).flatMap fun j => [a j, b j]

theorem pairsOf_length {M : ℕ} (a b : Fin M → ℕ) : (pairsOf a b).length = 2 * M := by
  induction M with
  | zero => simp [pairsOf]
  | succ M ih =>
    have := ih (fun j => a j.succ) (fun j => b j.succ)
    simp only [pairsOf, List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.length_append,
      List.length_cons, List.length_nil] at this ⊢
    omega

theorem pairsOf_get {M : ℕ} (a b : Fin M → ℕ) (i : Fin M) :
    litA (pairsOf a b) i.val = a i ∧ litB (pairsOf a b) i.val = b i := by
  induction M with
  | zero => exact i.elim0
  | succ M ih =>
    have e : pairsOf a b = [a 0, b 0] ++ pairsOf (fun j => a j.succ) (fun j => b j.succ) := by
      simp [pairsOf, List.finRange_succ, List.flatMap_map]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [litA, litB, e]
    · have := ih (fun j => a j.succ) (fun j => b j.succ) i'
      simp only [litA, litB, e] at this ⊢
      have h1 : 2 * (i'.succ : Fin (M + 1)).val = 2 * i'.val + 1 + 1 := by simp; ring
      rw [h1]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      simpa using this

theorem accW_pairs {M : ℕ} (a b : Fin M → ℕ) (Wc : ℕ → ℕ → List Bool) :
    accW (pairsOf a b) Wc M = (List.finRange M).flatMap fun i => Wc (a i) (b i) := by
  unfold accW
  rw [← finRange_map_val, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  obtain ⟨h1, h2⟩ := pairsOf_get a b i
  rw [h1, h2]

theorem accB_pairs {M : ℕ} (a b : Fin M → ℕ) (bc : ℕ → ℕ → Bool) :
    accB (pairsOf a b) bc M = (List.finRange M).all fun i => bc (a i) (b i) := by
  unfold accB
  rw [← finRange_map_val, List.all_map]
  exact all_congr_mem _ _ _ fun i _ => by
    obtain ⟨h1, h2⟩ := pairsOf_get a b i
    simp only [Function.comp_apply, h1, h2]

/-! ## The passes are the term lists -/

/-- The PCPP's literal list, clause by clause. -/
def litsD (D : UnionCheckData) : List ℕ :=
  pairsOf (fun i : Fin (2 ^ D.pcpp.clauseBits) => RepairRepresentation.literalIndex (D.pcpp.clauses i).left)
    (fun i => RepairRepresentation.literalIndex (D.pcpp.clauses i).right)

theorem magRegs_of (D : UnionCheckData) (Λ : ℕ) (v0 w : Fin NR → ℕ) (hmr : MagRegs D Λ v0)
    (hw : ∀ r, r ≠ rL0 → r ≠ rL1 → r ≠ rLIT → r ≠ rX → r ≠ rN0 → r ≠ rXS → r ≠ rSYSX → r ≠ rY → r ≠ rN1 → r ≠ rYS →
      w r = v0 r) : MagRegs D Λ w :=
  ⟨by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hmr.a,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hmr.b,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hmr.c,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hmr.d,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hmr.e,
   by rw [hw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hmr.f⟩

/-- A position's registers from a base: `LIT = ℓ`, only `L₁`/`LIT` differing from the base. -/
theorem pos_facts (D : UnionCheckData) (Λ : ℕ) (v0 w : Fin NR → ℕ) (hmr : MagRegs D Λ v0) (hSS : v0 rSS = D.s)
    (hSYS : v0 rSYS = D.pcpp.systematicBits) (hw : ∀ r, r ≠ rL1 → r ≠ rLIT → w r = v0 r) (X : PcppVar D.pcpp)
    (hL : w rLIT / 2 = X.val) :
    posRegs w rX = X.val ∧ posRegs w rXS = X.val * D.s ∧ posRegs w rSS = D.s ∧
      posRegs w rSYSX = (if D.sysBit X then 1 else 0) ∧ MagRegs D Λ (posRegs w) := by
  have hwS : w rSS = D.s := by rw [hw _ (by decide) (by decide), hSS]
  refine ⟨by rw [posRegs_X, hL], by rw [posRegs_XS, hL, hwS], ?_, ?_, ?_⟩
  · rw [posRegs_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide), hwS]
  · rw [posRegs_SYSX, hL, hw _ (by decide) (by decide), hSYS]
    simp [UnionCheckData.sysBit]
  · refine magRegs_of D Λ v0 _ hmr fun r h1 h2 h3 h4 h5 h6 h7 _ _ _ => ?_
    rw [posRegs_other _ _ h3 h5 h4 h6 h7, hw _ h2 h3]

/-- **The validity pass is `myV`'s entries.** -/
theorem accW_V_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v0 : Fin NR → ℕ) (Λ : ℕ) (hm : D.mass = Λ)
    (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hSS : v0 rSS = D.s)
    (hSYS : v0 rSYS = D.pcpp.systematicBits) (hmr : MagRegs D Λ v0) :
    accW (litsD D) (WVof d v0) (2 ^ D.pcpp.clauseBits) = (myV D).flatMap fun t => Entry.entryWord (entryOf 0 D.s t) := by
  unfold litsD
  rw [accW_pairs]
  unfold myV posList
  rw [List.flatMap_assoc, List.flatMap_assoc]
  apply List.flatMap_congr
  intro i _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WVof]
  rw [List.flatMap_assoc, List.flatMap_assoc]
  obtain ⟨a1, a2, a3, a4, a5⟩ := pos_facts D Λ v0 (Function.update (Function.update v0 rL1 (RepairRepresentation.literalIndex (D.pcpp.clauses i).right)) rLIT
      (RepairRepresentation.literalIndex (D.pcpp.clauses i).left)) hmr hSS hSYS
    (fun r h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]) (posVar D.pcpp i 0)
    (by simp [litIdx_div])
  obtain ⟨b1, b2, b3, b4, b5⟩ := pos_facts D Λ v0 (Function.update v0 rLIT (RepairRepresentation.literalIndex (D.pcpp.clauses i).right)) hmr hSS hSYS
    (fun r _ h2 => by rw [Function.update_of_ne h2])
    (posVar D.pcpp i 1) (by simp [litIdx_div])
  rw [outV_eq D d hr _ (i, 0) a1 a2 a3 a4 Λ hm hΛ hs hsg a5, outV_eq D d hr _ (i, 1) b1 b2 b3 b4 Λ hm hΛ hs hsg b5]

/-- **The second-moment pass is `myQ`'s entries.** -/
theorem accW_Q_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v0 : Fin NR → ℕ) (Λ : ℕ) (hm : D.mass = Λ)
    (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hSS : v0 rSS = D.s)
    (hSYS : v0 rSYS = D.pcpp.systematicBits) (hmr : MagRegs D Λ v0) :
    accW (litsD D) (WQof d v0) (2 ^ D.pcpp.clauseBits) = (myQ D).flatMap fun t => Entry.entryWord (entryOf 1 D.s t) := by
  unfold litsD
  rw [accW_pairs]
  unfold myQ posList
  rw [List.flatMap_assoc, List.flatMap_assoc]
  apply List.flatMap_congr
  intro i _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WQof]
  rw [List.flatMap_assoc, List.flatMap_assoc]
  obtain ⟨a1, a2, a3, -, a5⟩ := pos_facts D Λ v0 (Function.update (Function.update v0 rL1 (RepairRepresentation.literalIndex (D.pcpp.clauses i).right)) rLIT
      (RepairRepresentation.literalIndex (D.pcpp.clauses i).left)) hmr hSS hSYS
    (fun r h1 h2 => by rw [Function.update_of_ne h2, Function.update_of_ne h1]) (posVar D.pcpp i 0)
    (by simp [litIdx_div])
  obtain ⟨b1, b2, b3, -, b5⟩ := pos_facts D Λ v0 (Function.update v0 rLIT (RepairRepresentation.literalIndex (D.pcpp.clauses i).right)) hmr hSS hSYS
    (fun r _ h2 => by rw [Function.update_of_ne h2])
    (posVar D.pcpp i 1) (by simp [litIdx_div])
  rw [outQ_eq D d hr _ (i, 0) a1 a2 a3 Λ hm hΛ hs hsg a5, outQ_eq D d hr _ (i, 1) b1 b2 b3 Λ hm hΛ hs hsg b5]

/-- **The clause pass is `myMu`'s entries.** -/
theorem accW_Mu_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v0 : Fin NR → ℕ) (Λ : ℕ) (hm : D.mass = Λ)
    (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hSS : v0 rSS = D.s) (hmr : MagRegs D Λ v0) :
    accW (litsD D) (WMof d v0) (2 ^ D.pcpp.clauseBits) = (myMu D).flatMap fun t => Entry.entryWord (entryOf 2 D.s t) := by
  unfold litsD
  rw [accW_pairs]
  unfold myMu
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro i _
  simp only [WMof]
  rw [List.flatMap_assoc]
  set a := RepairRepresentation.literalIndex (D.pcpp.clauses i).left with ha
  set b := RepairRepresentation.literalIndex (D.pcpp.clauses i).right with hb
  have hmo : ∀ r, r ≠ rX → r ≠ rN0 → r ≠ rXS → r ≠ rY → r ≠ rN1 → r ≠ rYS → muRegs v0 a b r = v0 r :=
    fun r h1 h2 h3 h4 h5 h6 => muRegs_other v0 a b r h1 h2 h3 h4 h5 h6
  have hSS' : muRegs v0 a b rSS = D.s := by
    rw [hmo _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSS]
  refine outMu_eq D d hr _ i (by simp +decide [muRegs, Function.update_apply, ha, litIdx_div])
    (by simp +decide [muRegs, Function.update_apply, hb, litIdx_div])
    (by simp +decide [muRegs, Function.update_apply, ha, litIdx_div, hSS])
    (by simp +decide [muRegs, Function.update_apply, hb, litIdx_div, hSS]) hSS'
    (by simp +decide [muRegs, Function.update_apply, ha, litIdx_mod])
    (by simp +decide [muRegs, Function.update_apply, hb, litIdx_mod]) Λ hm hΛ hs hsg
    (magRegs_of D Λ v0 _ hmr fun r _ _ _ h4 h5 h6 _ h8 h9 h10 => hmo r h4 h5 h6 h8 h9 h10)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
